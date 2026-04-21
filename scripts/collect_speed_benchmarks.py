#!/usr/bin/env python3

import json
import subprocess
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
LEAN_BPE = ROOT / ".lake" / "build" / "bin" / "lean-bpe"
REPEATS = 3
CHECKPOINT = ROOT / "speed_benchmarks.partial.json"
DATASETS = [
    ("swe_bench", ROOT / "hf_benchmark_texts" / "swe_bench.txt"),
    ("gsm8k", ROOT / "hf_benchmark_texts" / "gsm8k.txt"),
    ("chemistryqa", ROOT / "hf_benchmark_texts" / "chemistryqa.txt"),
    ("bioasq", ROOT / "hf_benchmark_texts" / "bioasq.txt"),
    ("medmcqa", ROOT / "hf_benchmark_texts" / "medmcqa.txt"),
]
TOKENIZERS = [
    ("cl100k", ROOT / "tokenizers" / "cl100k" / "tokenizer.json"),
    ("o200k", ROOT / "tokenizers" / "o200k_harmony" / "tokenizer.json"),
]


def parse_lean_num_tokens(stdout: str) -> int:
    for line in stdout.splitlines():
        if "] num_tokens:" in line:
            return int(line.rsplit(": ", 1)[1])
    raise RuntimeError(f"failed to parse Lean benchmark output:\n{stdout}")


def run_timed_cmd(args: list[str]) -> tuple[str, float]:
    best_stdout: str | None = None
    best_elapsed: float | None = None
    for _ in range(REPEATS):
        start = time.perf_counter_ns()
        proc = subprocess.run(args, cwd=ROOT, capture_output=True, text=True)
        stop = time.perf_counter_ns()
        if proc.returncode != 0:
            raise RuntimeError(
                f"command failed: {' '.join(args)}\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
            )
        elapsed = (stop - start) / 1_000_000_000
        if best_elapsed is None or elapsed < best_elapsed:
            best_stdout = proc.stdout
            best_elapsed = elapsed
    assert best_stdout is not None
    assert best_elapsed is not None
    return best_stdout, best_elapsed


def run_lean(tokenizer_path: Path, dataset_path: Path) -> dict[str, float]:
    stdout, elapsed = run_timed_cmd(
        [
            str(LEAN_BPE),
            "--tokenizer",
            str(tokenizer_path),
            "bench",
            str(dataset_path),
        ]
    )
    num_tokens = parse_lean_num_tokens(stdout)
    return {
        "num_tokens": num_tokens,
        "total_time": elapsed,
        "tokens_per_sec": (0.0 if elapsed == 0.0 else num_tokens / elapsed),
    }


def run_tiktoken(tokenizer_path: Path, dataset_path: Path) -> dict[str, float]:
    stdout, elapsed = run_timed_cmd(
        [
            sys.executable,
            "scripts/benchmark_tiktoken.py",
            str(tokenizer_path),
            str(dataset_path),
        ]
    )
    payload = json.loads(stdout)
    num_tokens = int(payload["num_tokens"])
    return {
        "num_tokens": num_tokens,
        "total_time": elapsed,
        "tokens_per_sec": (0.0 if elapsed == 0.0 else num_tokens / elapsed),
    }


def main() -> int:
    total_steps = 2 * len(TOKENIZERS) * len(DATASETS)
    done_steps = 0
    rows: list[dict[str, object]] = []
    for engine in ("tiktoken", "LeanBPE"):
        for tokenizer_name, tokenizer_path in TOKENIZERS:
            row: dict[str, object] = {
                "engine": engine,
                "tokenizer": tokenizer_name,
                "datasets": {},
            }
            total_tokens = 0
            total_time = 0.0
            for dataset_name, dataset_path in DATASETS:
                print(
                    f"[{done_steps}/{total_steps}] running {engine} {tokenizer_name} on {dataset_name}",
                    file=sys.stderr,
                    flush=True,
                )
                metrics = (
                    run_tiktoken(tokenizer_path, dataset_path)
                    if engine == "tiktoken"
                    else run_lean(tokenizer_path, dataset_path)
                )
                row["datasets"][dataset_name] = {
                    "num_tokens": int(metrics["num_tokens"]),
                    "total_time": float(metrics["total_time"]),
                    "tokens_per_sec": float(metrics["tokens_per_sec"]),
                }
                total_tokens += int(metrics["num_tokens"])
                total_time += float(metrics["total_time"])
                done_steps += 1
                print(
                    f"[{done_steps}/{total_steps}] finished {engine} {tokenizer_name} on {dataset_name}",
                    file=sys.stderr,
                    flush=True,
                )
                CHECKPOINT.write_text(json.dumps(rows + [row], indent=2))
            row["overall"] = {
                "num_tokens": total_tokens,
                "total_time": total_time,
                "tokens_per_sec": (0.0 if total_time == 0.0 else total_tokens / total_time),
            }
            rows.append(row)
            CHECKPOINT.write_text(json.dumps(rows, indent=2))
    print(json.dumps(rows, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
