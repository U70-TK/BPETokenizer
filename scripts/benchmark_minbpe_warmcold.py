#!/usr/bin/env python3

import json
import resource
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "minbpe"))
from minbpe import GPT4Tokenizer  # noqa: E402


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


def run_pass(tok: GPT4Tokenizer, samples: list[str]) -> dict[str, float]:
    token_total = 0
    start = time.perf_counter_ns()
    for sample in samples:
        token_total += len(tok.encode_ordinary(sample))
    stop = time.perf_counter_ns()
    total_time = (stop - start) / 1_000_000_000
    return {
        "num_tokens": token_total,
        "total_time": total_time,
        "tokens_per_sec": 0.0 if total_time == 0 else token_total / total_time,
    }


def main() -> int:
    if len(sys.argv) != 3:
        print(
            "usage: benchmark_minbpe_warmcold.py <tokenizer.json> <dataset.txt>",
            file=sys.stderr,
        )
        return 2

    tokenizer_path = Path(sys.argv[1])
    dataset_path = Path(sys.argv[2])
    samples = load_samples(dataset_path)
    if any(any(ord(c) >= 128 for c in sample) for sample in samples):
        print("only ASCII benchmark inputs are supported", file=sys.stderr)
        return 2

    tok = GPT4Tokenizer(tokenizer_path=str(tokenizer_path))
    stats = run_pass(tok, samples)
    payload = {
        "tokenizer": str(tokenizer_path),
        "dataset": str(dataset_path),
        "num_tokens": stats["num_tokens"],
        "total_time": stats["total_time"],
        "tokens_per_sec": stats["tokens_per_sec"],
        "peak_rss_bytes": max_rss_bytes(),
    }
    print(json.dumps(payload))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
