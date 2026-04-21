# LeanBPETokenizer

Lean formalization of an ASCII-only BPE tokenizer with a verified encode/decode
core and a validated runtime bridge from selected `tokenizer.json` files.

## Scope

- Supported tokenizer families: `cl100k` and `o200k`
- Supported inputs: ASCII strings only
- Unsupported tokenizer family: GPT-2 / `ByteLevel`
- Supported packaged JSONs:
  - `tokenizers/cl100k/tokenizer.json`
  - `tokenizers/o200k_harmony/tokenizer.json`

## What Is Proved

- The abstract BPE pipeline roundtrips on ASCII input once the merge table and
  vocabulary satisfy the proof-facing invariants.
- `ValidMergeList` is sufficient to build the abstract `EncodeReady` witness
  used by the roundtrip theorem.
- A loaded runtime tokenizer that passes
  `validateLoadedAsciiTokenizer` yields a proof-carrying
  `LoadedAsciiSound` certificate.
- External-id encode/decode roundtrips for certified loaded tokenizers.
- The ASCII pretokenizer preserves the input partition property.
- The `cl100k` and `o200k` ASCII pretokenizers now have explicit
  correspondence theorems against the supported ASCII-specialized regex spec.

## What Is Not Proved

- The raw JSON parser is not verified.
- JSON extraction is validated after loading; it is not proved correct by
  construction from file bytes.
- Unicode behavior is out of scope.
- GPT-2 `ByteLevel` pretokenization is out of scope.

## Build

```bash
lake update
lake exe cache get
lake build
```

## CLI

```bash
lake build lean-bpe
.lake/build/bin/lean-bpe info
.lake/build/bin/lean-bpe check
.lake/build/bin/lean-bpe --tokenizer tokenizers/cl100k/tokenizer.json roundtrip "don't stop"
```

## Current Theorem Boundary

The strongest end-to-end theorem in the packaged runtime path is:

- load JSON
- extract an ASCII tokenizer artifact
- validate that artifact
- obtain `LoadedAsciiSound`
- conclude external-id roundtrip for ASCII input

So the runtime bridge is theorem-backed after successful validation, but the
project does not yet prove correctness of the JSON parser itself.
