#!/usr/bin/env python3

import json
import sys
from pathlib import Path

import tiktoken


def byte_to_unicode():
    bs = list(range(ord("!"), ord("~") + 1))
    bs += list(range(ord("¡"), ord("¬") + 1))
    bs += list(range(ord("®"), ord("ÿ") + 1))
    cs = bs[:]
    n = 0
    for b in range(256):
        if b not in bs:
            bs.append(b)
            cs.append(256 + n)
            n += 1
    return dict(zip(bs, map(chr, cs)))


BYTE_TO_UNICODE = byte_to_unicode()
UNICODE_TO_BYTE = {v: k for k, v in BYTE_TO_UNICODE.items()}


def decode_token(token: str) -> bytes:
    return bytes(UNICODE_TO_BYTE[c] for c in token)


def build_encoding(tokenizer_path: Path) -> tiktoken.Encoding:
    with tokenizer_path.open() as f:
        data = json.load(f)
    pat_str = data["pre_tokenizer"]["pretokenizers"][0]["pattern"]["Regex"]
    mergeable_ranks = {
        decode_token(token): token_id for token, token_id in data["model"]["vocab"].items()
    }
    special_tokens = {
        entry["content"]: entry["id"]
        for entry in data.get("added_tokens", [])
        if entry.get("special")
    }
    return tiktoken.Encoding(
        name=tokenizer_path.stem,
        pat_str=pat_str,
        mergeable_ranks=mergeable_ranks,
        special_tokens=special_tokens,
    )


def main() -> int:
    if len(sys.argv) != 3:
        print("usage: tiktoken_encode.py <tokenizer.json> <text>", file=sys.stderr)
        return 2
    tokenizer_path = Path(sys.argv[1])
    text = sys.argv[2]
    if any(ord(c) >= 128 for c in text):
        print("only ASCII test inputs are supported", file=sys.stderr)
        return 2
    enc = build_encoding(tokenizer_path)
    ids = enc.encode(text)
    print(",".join(str(i) for i in ids))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
