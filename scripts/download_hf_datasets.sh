#!/usr/bin/env bash

set -euo pipefail

ROOT_DIR="${1:-hf_datasets}"

DATASETS=(
  "SWE-bench/SWE-bench"
  "openai/gsm8k"
  "avaliev/ChemistryQA"
  "jmhb/BioASQ"
  "openlifescienceai/medmcqa"
)

mkdir -p "$ROOT_DIR"

for dataset in "${DATASETS[@]}"; do
  target="$ROOT_DIR/$dataset"
  mkdir -p "$target"
  echo "Downloading $dataset -> $target"
  hf download "$dataset" \
    --repo-type dataset \
    --local-dir "$target"
done
