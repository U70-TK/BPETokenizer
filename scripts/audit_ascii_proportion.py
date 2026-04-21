#!/usr/bin/env python3

from __future__ import annotations

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


@dataclass
class Stats:
    examples: int = 0
    non_ascii_examples: int = 0

    def add_example(self, has_non_ascii: bool) -> None:
        self.examples += 1
        if has_non_ascii:
            self.non_ascii_examples += 1

    def merge(self, other: "Stats") -> None:
        self.examples += other.examples
        self.non_ascii_examples += other.non_ascii_examples

    @property
    def proportion(self) -> float:
        if self.examples == 0:
            return 0.0
        return self.non_ascii_examples / self.examples


def row_has_non_ascii(row) -> bool:
    saw_text = False
    for text in iter_strings(row):
        saw_text = True
        if not is_ascii_text(text):
            return True
    return False if saw_text else False


def audit_jsonl(path: Path) -> Stats:
    stats = Stats()
    with path.open() as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            obj = json.loads(line)
            stats.add_example(row_has_non_ascii(obj))
    return stats


def audit_json(path: Path) -> Stats:
    stats = Stats()
    with path.open() as f:
        obj = json.load(f)
    if isinstance(obj, list):
        for row in obj:
            stats.add_example(row_has_non_ascii(row))
    else:
        stats.add_example(row_has_non_ascii(obj))
    return stats


def audit_text(path: Path) -> Stats:
    stats = Stats()
    with path.open() as f:
        for line in f:
            stats.add_example(not is_ascii_text(line.rstrip("\n")))
    return stats


def audit_parquet(path: Path) -> Stats:
    stats = Stats()
    parquet = pq.ParquetFile(path)
    for batch in parquet.iter_batches():
      rows = batch.to_pylist()
      for row in rows:
          stats.add_example(row_has_non_ascii(row))
    return stats


def audit_file(path: Path) -> Stats:
    suffixes = path.suffixes
    if suffixes[-2:] == [".jsonl", ".gz"]:
        raise RuntimeError(f"unsupported compressed JSONL file: {path}")
    if path.suffix == ".parquet":
        return audit_parquet(path)
    if path.suffix == ".jsonl":
        return audit_jsonl(path)
    if path.suffix == ".json":
        return audit_json(path)
    if path.suffix in {".txt", ".md", ".csv"}:
        return audit_text(path)
    return Stats()


def main() -> int:
    root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("hf_datasets")
    if not root.exists():
        print(f"dataset root does not exist: {root}", file=sys.stderr)
        return 2

    overall = Stats()
    dataset_dirs = sorted(path for path in root.iterdir() if path.is_dir())
    for dataset_dir in dataset_dirs:
        stats = Stats()
        for path in sorted(dataset_dir.rglob("*")):
            if path.is_file():
                stats.merge(audit_file(path))
        overall.merge(stats)
        print(
            json.dumps(
                {
                    "dataset": dataset_dir.name,
                    "examples": stats.examples,
                    "non_ascii_examples": stats.non_ascii_examples,
                    "proportion_non_ascii": stats.proportion,
                }
            )
        )

    print(
        json.dumps(
            {
                "dataset": "__overall__",
                "examples": overall.examples,
                "non_ascii_examples": overall.non_ascii_examples,
                "proportion_non_ascii": overall.proportion,
            }
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
