#!/usr/bin/env python3

import json
import sys
from pathlib import Path

from tiktoken_encode import build_encoding


def main() -> int:
    if len(sys.argv) != 3:
        print(
            "usage: tiktoken_batch_encode.py <tokenizer.json> <samples.json>",
            file=sys.stderr,
        )
        return 2
    tokenizer_path = Path(sys.argv[1])
    samples_path = Path(sys.argv[2])
    with samples_path.open() as f:
        samples = json.load(f)
    if not isinstance(samples, list) or not all(isinstance(s, str) for s in samples):
        print("samples file must be a JSON array of strings", file=sys.stderr)
        return 2
    if any(any(ord(c) >= 128 for c in sample) for sample in samples):
        print("only ASCII test inputs are supported", file=sys.stderr)
        return 2
    enc = build_encoding(tokenizer_path)
    rows = [enc.encode(sample, disallowed_special=()) for sample in samples]
    print(json.dumps(rows))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
