#!/usr/bin/env python3

import json
import resource
import sys
import time
from pathlib import Path

from tiktoken_encode import build_encoding


def load_samples(dataset_path: Path) -> list[str]:
    with dataset_path.open() as f:
        rows = [line.rstrip("\n\r") for line in f]
    if rows and rows[-1] == "":
        rows.pop()
    return rows


def max_rss_bytes() -> int:
    val = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    if sys.platform == "darwin":
        return int(val)
    return int(val) * 1024


def main() -> int:
    if len(sys.argv) != 3:
        print(
            "usage: benchmark_tiktoken_warmcold.py <tokenizer.json> <dataset.txt>",
            file=sys.stderr,
        )
        return 2

    tokenizer_path = Path(sys.argv[1])
    dataset_path = Path(sys.argv[2])
    enc = build_encoding(tokenizer_path)
    samples = load_samples(dataset_path)
    if any(any(ord(c) >= 128 for c in sample) for sample in samples):
        print("only ASCII benchmark inputs are supported", file=sys.stderr)
        return 2

    token_total = 0
    start = time.perf_counter_ns()
    for sample in samples:
        token_total += len(enc.encode(sample, disallowed_special=()))
    stop = time.perf_counter_ns()
    total_time = (stop - start) / 1_000_000_000

    payload = {
        "tokenizer": str(tokenizer_path),
        "dataset": str(dataset_path),
        "num_tokens": token_total,
        "total_time": total_time,
        "tokens_per_sec": 0.0 if total_time == 0 else token_total / total_time,
        "peak_rss_bytes": max_rss_bytes(),
    }
    print(json.dumps(payload))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
