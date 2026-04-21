#!/usr/bin/env python3

import json
import subprocess
import time
from pathlib import Path

try:
    from tqdm import tqdm
except Exception:  # pragma: no cover
    class _SimplePbar:
        def __init__(self, total: int, desc: str, unit: str):
            self.total = total
            self.done = 0
            self.desc = desc
            self.unit = unit
            print(f"{desc}: 0/{total} {unit}")

        def update(self, n: int) -> None:
            self.done += n
            print(f"{self.desc}: {self.done}/{self.total} {self.unit}")

        def close(self) -> None:
            pass

    def tqdm(total: int, desc: str, unit: str):
        return _SimplePbar(total, desc, unit)


ROOT = Path(__file__).resolve().parent.parent
LEAN_BPE = ROOT / ".lake" / "build" / "bin" / "lean-bpe"

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


def run_with_peak_rss(args: list[str]) -> tuple[int, str, str, int]:
    # Fallback when psutil is unavailable.
    try:
        import psutil  # type: ignore
    except Exception:  # pragma: no cover
        psutil = None

    proc = subprocess.Popen(
        args,
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    peak = 0
    child = psutil.Process(proc.pid) if psutil is not None else None
    while proc.poll() is None:
        if child is not None:
            try:
                rss = child.memory_info().rss
                if rss > peak:
                    peak = rss
            except Exception:
                child = None
        time.sleep(0.01)
    stdout, stderr = proc.communicate()
    if child is not None:
        try:
            rss = child.memory_info().rss
            if rss > peak:
                peak = rss
        except Exception:
            pass
    return proc.returncode, stdout, stderr, peak


def run_lean(tokenizer_path: Path, dataset_path: Path) -> dict[str, float | int]:
    args = [
        str(LEAN_BPE),
        "--tokenizer",
        str(tokenizer_path),
        "bench",
        str(dataset_path),
    ]
    returncode, stdout, stderr, peak_rss = run_with_peak_rss(args)
    if returncode != 0:
        raise RuntimeError(
            f"lean-bpe bench failed\nstdout:\n{stdout}\nstderr:\n{stderr}"
        )
    num_tokens = parse_lean_num_tokens(stdout)
    total_time = 0.0
    for line in stdout.splitlines():
        if "] total_time:" in line:
            total_time = float(line.rsplit(": ", 1)[1].removesuffix("s"))
            break
    if total_time == 0.0:
        raise RuntimeError(f"failed to parse Lean total_time from output:\n{stdout}")
    return {
        "num_tokens": num_tokens,
        "total_time": total_time,
        "tokens_per_sec": 0.0 if total_time == 0 else num_tokens / total_time,
        "peak_rss_bytes": peak_rss,
    }


def run_tiktoken(tokenizer_path: Path, dataset_path: Path) -> dict[str, float | int]:
    proc = subprocess.run(
        [
            "python3",
            "scripts/benchmark_tiktoken_warmcold.py",
            str(tokenizer_path),
            str(dataset_path),
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"benchmark_tiktoken_warmcold.py failed\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        )
    payload = json.loads(proc.stdout)
    return {
        "num_tokens": int(payload["num_tokens"]),
        "total_time": float(payload["total_time"]),
        "tokens_per_sec": float(payload["tokens_per_sec"]),
        "peak_rss_bytes": int(payload["peak_rss_bytes"]),
    }


def run_minbpe(tokenizer_path: Path, dataset_path: Path) -> dict[str, float | int]:
    proc = subprocess.run(
        [
            "python3",
            "scripts/benchmark_minbpe_warmcold.py",
            str(tokenizer_path),
            str(dataset_path),
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"benchmark_minbpe_warmcold.py failed\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        )
    payload = json.loads(proc.stdout)
    return {
        "num_tokens": int(payload["num_tokens"]),
        "total_time": float(payload["total_time"]),
        "tokens_per_sec": float(payload["tokens_per_sec"]),
        "peak_rss_bytes": int(payload["peak_rss_bytes"]),
    }


def main() -> int:
    out_path = ROOT / "speed_benchmarks_3engines.json"
    rows: list[dict[str, object]] = []
    engines = ("tiktoken", "MinBPE", "LeanBPE")
    steps = len(engines) * len(TOKENIZERS) * len(DATASETS)
    pbar = tqdm(total=steps, desc="bench sweeps", unit="sweep")

    for engine in engines:
        for tokenizer_name, tokenizer_path in TOKENIZERS:
            row: dict[str, object] = {"engine": engine, "tokenizer": tokenizer_name, "datasets": {}}
            total_tokens = 0
            total_time = 0.0
            peak_rss_bytes = 0
            for dataset_name, dataset_path in DATASETS:
                metrics = (
                    run_tiktoken(tokenizer_path, dataset_path)
                    if engine == "tiktoken"
                    else run_minbpe(tokenizer_path, dataset_path)
                    if engine == "MinBPE"
                    else run_lean(tokenizer_path, dataset_path)
                )
                row["datasets"][dataset_name] = metrics
                total_tokens += int(metrics["num_tokens"])
                total_time += float(metrics["total_time"])
                peak_rss_bytes = max(peak_rss_bytes, int(metrics["peak_rss_bytes"]))
                pbar.update(1)
            row["overall"] = {
                "num_tokens": total_tokens,
                "total_time": total_time,
                "tokens_per_sec": 0.0 if total_time == 0 else total_tokens / total_time,
                "peak_rss_bytes": peak_rss_bytes,
            }
            rows.append(row)
            out_path.write_text(json.dumps(rows, indent=2))
    pbar.close()
    out_path.write_text(json.dumps(rows, indent=2))
    print(json.dumps(rows, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
