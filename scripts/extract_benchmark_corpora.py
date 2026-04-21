#!/usr/bin/env python3

import json
import sys
from pathlib import Path


DATASETS = [
    (
        "swe_bench",
        Path("hf_datasets_ascii/SWE-bench/SWE-bench/ascii_only.jsonl"),
        "problem_statement",
    ),
    (
        "gsm8k",
        Path("hf_datasets_ascii/openai/gsm8k/ascii_only.jsonl"),
        "question",
    ),
    (
        "chemistryqa",
        Path("hf_datasets_ascii/avaliev/ChemistryQA/ascii_only.jsonl"),
        "question",
    ),
    (
        "bioasq",
        Path("hf_datasets_ascii/jmhb/BioASQ/ascii_only.jsonl"),
        "question",
    ),
    (
        "medmcqa",
        Path("hf_datasets_ascii/openlifescienceai/medmcqa/ascii_only.jsonl"),
        "question",
    ),
]


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: extract_benchmark_corpora.py <output-dir>", file=sys.stderr)
        return 2
    out_root = Path(sys.argv[1])
    out_root.mkdir(parents=True, exist_ok=True)
    for name, src, field in DATASETS:
        rows = 0
        kept = 0
        out_path = out_root / f"{name}.txt"
        with src.open() as f, out_path.open("w") as out:
            for line in f:
                rows += 1
                obj = json.loads(line)
                text = obj.get(field)
                if not isinstance(text, str):
                    continue
                if not text:
                    continue
                if any(ord(c) >= 128 for c in text):
                    continue
                out.write(text.replace("\n", " ").replace("\r", " "))
                out.write("\n")
                kept += 1
        print(
            json.dumps(
                {
                    "dataset": name,
                    "source": str(src),
                    "field": field,
                    "rows_seen": rows,
                    "texts_written": kept,
                    "output": str(out_path),
                }
            )
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
