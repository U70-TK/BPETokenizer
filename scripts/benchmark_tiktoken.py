#!/usr/bin/env python3

import json
import sys
import time
from pathlib import Path

from tiktoken_encode import build_encoding


def load_samples(dataset_path: Path) -> list[str]:
    with dataset_path.open() as f:
        samples = [line.rstrip("\n\r") for line in f]
    if samples and samples[-1] == "":
        samples.pop()
    return samples


def main() -> int:
    if len(sys.argv) != 3:
        print("usage: benchmark_tiktoken.py <tokenizer.json> <dataset.txt>", file=sys.stderr)
        return 2
    tokenizer_path = Path(sys.argv[1])
    dataset_path = Path(sys.argv[2])
    samples = load_samples(dataset_path)
    if any(any(ord(c) >= 128 for c in sample) for sample in samples):
        print("only ASCII benchmark inputs are supported", file=sys.stderr)
        return 2
    enc = build_encoding(tokenizer_path)
    token_total = 0
    start = time.perf_counter_ns()
    for sample in samples:
        token_total += len(enc.encode(sample, disallowed_special=()))
    stop = time.perf_counter_ns()
    elapsed_ns = stop - start
    elapsed_s = elapsed_ns / 1_000_000_000
    tokens_per_sec = 0.0 if elapsed_ns == 0 else token_total / elapsed_s
    print(
        json.dumps(
            {
                "tokenizer": str(tokenizer_path),
                "dataset": str(dataset_path),
                "samples": len(samples),
                "num_tokens": token_total,
                "total_time": elapsed_s,
                "tokens_per_sec": tokens_per_sec,
            }
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
