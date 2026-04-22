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

## Experiment Replication

To generate the full benchmark text corpora used by scripts in this repo:

```bash
# 1) Download datasets from Hugging Face
bash scripts/download_hf_datasets.sh hf_datasets

# 2) (Optional) Audit non-ASCII proportion in raw datasets
python3 scripts/audit_ascii_proportion.py hf_datasets

# 3) Filter to ASCII-only records
python3 scripts/filter_ascii_records.py hf_datasets hf_datasets_ascii

# 4) Extract plain-text corpora
python3 scripts/extract_benchmark_corpora.py hf_datasets_text

# 5) Prepare benchmark input path expected by benchmark scripts
mkdir -p hf_benchmark_texts
cp hf_datasets_text/*.txt hf_benchmark_texts/

# 6) Build CLI binary
lake build lean-bpe

# 7) Run correctness studies (writes .out logs under study_results/)
mkdir -p study_results
for tok in tokenizers/cl100k/tokenizer.json tokenizers/o200k_harmony/tokenizer.json; do
  for ds in swe_bench gsm8k chemistryqa bioasq medmcqa; do
    .lake/build/bin/lean-bpe --tokenizer "$tok" study "hf_benchmark_texts/$ds.txt" \
      > "study_results/$(basename "$(dirname "$tok")")_${ds}.out"
  done
done

# 8) Run benchmark scripts (pick one based on what you need)
# 8a) LeanBPE vs tiktoken (writes speed_benchmarks.partial.json + stdout JSON)
python3 scripts/collect_speed_benchmarks.py > speed_benchmarks_2engines.json

# 8b) 3-engine speed+memory (writes speed_benchmarks_3engines.json)
# script name is legacy
python3 scripts/compare_warm_cold.py

# 9) (Optional) Create benchmark_runs/ by repeating a benchmark and copying outputs
mkdir -p benchmark_runs
for i in 1 2 3 4 5; do
  python3 scripts/compare_warm_cold.py
  cp speed_benchmarks_3engines.json "benchmark_runs/speed_benchmarks_3engines_run${i}.json"
done
```

This produces:

- `hf_datasets_text/swe_bench.txt`
- `hf_datasets_text/gsm8k.txt`
- `hf_datasets_text/chemistryqa.txt`
- `hf_datasets_text/bioasq.txt`
- `hf_datasets_text/medmcqa.txt`

Notes:

- Step 4 extracts configured fields (`problem_statement` or `question`), not all
  dataset columns.
- Requirements: `hf` CLI installed/authenticated and Python dependency
  `pyarrow`.
- `benchmark_runs/` is not auto-created by a single script in this repo; it is
  typically produced by repeating a benchmark command and archiving each run's
  JSON output.

## Current Theorem Boundary

The strongest end-to-end theorem in the packaged runtime path is:

- load JSON
- extract an ASCII tokenizer artifact
- validate that artifact
- obtain `LoadedAsciiSound`
- conclude external-id roundtrip for ASCII input

So the runtime bridge is theorem-backed after successful validation, but the
project does not yet prove correctness of the JSON parser itself.
