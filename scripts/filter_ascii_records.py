#!/usr/bin/env python3

from __future__ import annotations

import csv
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

import pyarrow.parquet as pq


def is_ascii_text(text: str) -> bool:
    return all(ord(ch) < 128 for ch in text)


def iter_strings(value) -> Iterable[str]:
    if isinstance(value, str):
        yield value
    elif isinstance(value, dict):
        for nested in value.values():
            yield from iter_strings(nested)
    elif isinstance(value, (list, tuple)):
        for nested in value:
            yield from iter_strings(nested)


def row_has_non_ascii(row) -> bool:
    return any(not is_ascii_text(text) for text in iter_strings(row))


@dataclass
class FilterStats:
    examples: int = 0
    kept_ascii_examples: int = 0

    def add(self, kept: bool) -> None:
        self.examples += 1
        if kept:
            self.kept_ascii_examples += 1


def emit_rows_jsonl(rows: Iterable[object], out_path: Path, stats: FilterStats) -> None:
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w") as f:
        for row in rows:
            keep = not row_has_non_ascii(row)
            stats.add(keep)
            if keep:
                f.write(json.dumps(row, ensure_ascii=True) + "\n")


def rows_from_parquet(path: Path) -> Iterable[object]:
    parquet = pq.ParquetFile(path)
    for batch in parquet.iter_batches():
        yield from batch.to_pylist()


def rows_from_jsonl(path: Path) -> Iterable[object]:
    with path.open() as f:
        for line in f:
            line = line.strip()
            if line:
                yield json.loads(line)


def rows_from_json(path: Path) -> Iterable[object]:
    with path.open() as f:
        obj = json.load(f)
    if isinstance(obj, list):
        yield from obj
    else:
        yield obj


def rows_from_delimited(path: Path, delimiter: str) -> Iterable[object]:
    with path.open(newline="") as f:
        reader = csv.DictReader(f, delimiter=delimiter)
        yield from reader


def rows_from_text(path: Path) -> Iterable[object]:
    with path.open() as f:
        for line in f:
            yield {"text": line.rstrip("\n")}


def rows_from_file(path: Path) -> Iterable[object]:
    suffixes = path.suffixes
    if suffixes[-2:] == [".jsonl", ".gz"]:
        raise RuntimeError(f"unsupported compressed JSONL file: {path}")
    if path.suffix == ".parquet":
        yield from rows_from_parquet(path)
    elif path.suffix == ".jsonl":
        yield from rows_from_jsonl(path)
    elif path.suffix == ".json":
        yield from rows_from_json(path)
    elif path.suffix == ".csv":
        yield from rows_from_delimited(path, ",")
    elif path.suffix == ".tsv":
        yield from rows_from_delimited(path, "\t")
    elif path.suffix in {".txt", ".md"}:
        yield from rows_from_text(path)


def collect_dataset_dirs(root: Path) -> list[Path]:
    nested = [
        dataset_dir
        for owner_dir in sorted(root.iterdir())
        if owner_dir.is_dir()
        for dataset_dir in sorted(owner_dir.iterdir())
        if dataset_dir.is_dir()
    ]
    if nested:
        return nested
    return [path for path in sorted(root.iterdir()) if path.is_dir()]


def main() -> int:
    src_root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("hf_datasets")
    dst_root = Path(sys.argv[2]) if len(sys.argv) > 2 else Path("hf_datasets_ascii")
    if not src_root.exists():
        print(f"dataset root does not exist: {src_root}", file=sys.stderr)
        return 2

    dataset_dirs = collect_dataset_dirs(src_root)
    for dataset_dir in dataset_dirs:
        rel = dataset_dir.relative_to(src_root)
        out_path = dst_root / rel / "ascii_only.jsonl"
        stats = FilterStats()

        def all_rows():
            for path in sorted(dataset_dir.rglob("*")):
                if path.is_file():
                    yield from rows_from_file(path)

        emit_rows_jsonl(all_rows(), out_path, stats)
        print(
            json.dumps(
                {
                    "dataset": rel.as_posix(),
                    "examples": stats.examples,
                    "kept_ascii_examples": stats.kept_ascii_examples,
                    "retention_ratio": (
                        0.0 if stats.examples == 0 else stats.kept_ascii_examples / stats.examples
                    ),
                    "output": out_path.as_posix(),
                }
            )
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
