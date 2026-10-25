#!/usr/bin/env python3
"""Run the Appendix A experiments and save compact CSV results and paper graphs."""
import csv
import os
import statistics
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

import matplotlib.pyplot as plt

# Settings to change for the experiments.
PERFORMANCE_N = 10
PERFORMANCE_K = [10, 20, 30, 40, 50, 60]
SELECTED_HEURISTIC = "prune+invariants"
PERFORMANCE_MODES = ["none", SELECTED_HEURISTIC, "all"]
PERFORMANCE_REPEATS = 1  # Use 3 for more stable final measurements.
RUN_PERFORMANCE_EXPERIMENT = True
MUTANT_N = range(2, 11)
COMPLETENESS_MODE = "all"
DEFAULT_K = 50
K_BY_BENCHMARK = {name: 50 for name in ("memberOf", "divByN", "pullUp", "bsort", "find12", "min")}
# Keep performance runs serial so concurrent processes do not distort timings.
PERFORMANCE_TIMEOUT_SECONDS = 1500
PERFORMANCE_INVARIANT_TIMEOUT_MS = 1000

# Completeness runs many independent mutant cases, so these run in parallel.
COMPLETENESS_TIMEOUT_SECONDS = 300
COMPLETENESS_INVARIANT_TIMEOUT_MS = 1000
MAX_WORKERS = min(4, os.cpu_count() or 1)  # Raise/lower to fit your machine.

# Find the project root whether run from the root or from src/scripts/.
HERE = Path(__file__).absolute()
CWD = Path.cwd()
ROOT = CWD if (CWD / "GCLparser.cabal").is_file() else HERE.parents[2]

if not (ROOT / "GCLparser.cabal").is_file():
    raise SystemExit("Run this script from the project root, or place it in src/scripts/.")

BENCH = ROOT / "examples" / "GCL" / "benchmark"
MUTANTS = BENCH / "mutants"
OUT = ROOT / "results" / "appendix"
GRAPHS = OUT / "graphs"
ORIGINALS = {name: BENCH / f"{name}.gcl" for name in ("memberOf", "divByN", "pullUp")}
INVALID_STEMS = {name: f"invalid{name[0].upper()}{name[1:]}" for name in ("memberOf", "divByN", "pullUp", "bsort", "find12", "min")}
COLUMNS = [
    "experiment", "benchmark", "case_kind", "file", "N", "K", "heuristics",
    "expected_verdict", "verdict", "kill", "elapsed_seconds", "wall_seconds", "paths_inspected",
    "paths_pruned", "full_paths_generated", "paths_verified", "total_wlp_size",
    "invariant_status", "run_status", "error",
]

def clean_path(path):
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)

def find_invalids():
    found = {}
    for name, stem in INVALID_STEMS.items():
        for path in BENCH.rglob("*.gcl"):
            if MUTANTS not in path.parents and path.stem.lower() == stem.lower():
                found[name] = path
                break
    return found

def find_mutants():
    found = {}
    if not MUTANTS.is_dir():
        raise FileNotFoundError(f"Mutant folder not found: {MUTANTS}")
    for path in sorted(MUTANTS.rglob("*.gcl")):
        relative = path.relative_to(MUTANTS)
        name = relative.parts[0] if len(relative.parts) > 1 else path.stem.split("_")[0]
        found.setdefault(name, []).append(path)
    return found

def build_main():
    def run(args):
        return subprocess.run(args, cwd=ROOT, text=True, capture_output=True)

    build = run(["cabal", "build", "exe:Main"])
    if build.returncode:
        raise RuntimeError((build.stdout + "\n" + build.stderr)[-5000:])
    listed = run(["cabal", "list-bin", "exe:Main"])
    if listed.returncode:
        raise RuntimeError((listed.stdout + "\n" + listed.stderr)[-3000:])
    exe = Path(listed.stdout.strip().splitlines()[-1])
    if not exe.is_absolute():
        exe = ROOT / exe
    if not exe.is_file():
        raise FileNotFoundError(f"Cabal executable not found: {exe}")
    return exe

def parse_result(stdout):
    keys = ["benchmark", "file", "N", "K", "heuristics", "verdict", "elapsed_seconds", "paths_inspected", "paths_pruned", "full_paths_generated", "paths_verified", "total_wlp_size", "invariant_status"]
    for line in stdout.splitlines():
        if line.startswith("BENCHMARK_RESULT\t"):
            values = line.split("\t")[1:]
            if len(values) == len(keys):
                return dict(zip(keys, values))
    return None


def run_case(exe, experiment, benchmark, kind, file, n, k, mode, invariant_timeout_ms, run_timeout_seconds):
    started = time.perf_counter()
    cmd = [str(exe), "--benchmark", "--file", str(file), "--k", str(k), "--n", str(n), "--heuristics", mode, "--invariant-timeout-ms", str(invariant_timeout_ms)]
    try:
        proc = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=run_timeout_seconds)
        result = parse_result(proc.stdout)
        wall = time.perf_counter() - started
        if result is None:
            detail = (proc.stderr or proc.stdout or f"exit code {proc.returncode}")[-1500:]
            return failed_row(experiment, benchmark, kind, file, n, k, mode, "ERROR", wall, detail)
        verdict = result["verdict"]
        expected = {"original": "ACCEPT", "invalid_control": "REJECT"}.get(kind, "NOT_KNOWN")
        killed = kind == "mutant" and verdict == "REJECT"
        if verdict in ("ERROR", "TIMEOUT", "UNSUPPORTED"):
            status = verdict.lower()
        elif verdict not in ("ACCEPT", "REJECT"):
            status = "inconclusive"
        elif expected != "NOT_KNOWN" and verdict != expected:
            status = "unexpected_result"
        else:
            status = "completed"
        return {
            "experiment": experiment, "benchmark": benchmark, "case_kind": kind,
            "file": clean_path(file), "N": n, "K": k, "heuristics": mode,
            "expected_verdict": expected, "verdict": verdict, "kill": str(killed).lower(),
            "elapsed_seconds": result["elapsed_seconds"], "wall_seconds": f"{wall:.3f}",
            "paths_inspected": result["paths_inspected"], "paths_pruned": result["paths_pruned"],
            "full_paths_generated": result["full_paths_generated"],
            "paths_verified": result["paths_verified"], "total_wlp_size": result["total_wlp_size"],
            "invariant_status": result["invariant_status"], "run_status": status, "error": "",
        }
    except subprocess.TimeoutExpired:
        return failed_row(experiment, benchmark, kind, file, n, k, mode, "TIMEOUT", time.perf_counter() - started, f"Exceeded {run_timeout_seconds}s")
    except Exception as exc:
        return failed_row(experiment, benchmark, kind, file, n, k, mode, "ERROR", time.perf_counter() - started, str(exc))


def failed_row(experiment, benchmark, kind, file, n, k, mode, verdict, wall, error):
    row = {key: "" for key in COLUMNS}
    expected = {"original": "ACCEPT", "invalid_control": "REJECT"}.get(kind, "NOT_KNOWN")
    row.update(experiment=experiment, benchmark=benchmark, case_kind=kind, file=clean_path(file), N=n, K=k, heuristics=mode, expected_verdict=expected, verdict=verdict, kill="false", wall_seconds=f"{wall:.3f}", run_status=verdict.lower(), error=error)
    return row

def reset_csv(path):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as f:
        csv.DictWriter(f, fieldnames=COLUMNS).writeheader()

def append_csv(path, row):
    with path.open("a", newline="", encoding="utf-8") as f:
        csv.DictWriter(f, fieldnames=COLUMNS).writerow(row)

def performance_graph(rows):
    GRAPHS.mkdir(parents=True, exist_ok=True)
    # One figure, with one small panel per required benchmark; only runtime is graphed.
    fig, axes = plt.subplots(1, len(ORIGINALS), figsize=(11, 3.5), sharey=True)
    for ax, benchmark in zip(axes, ORIGINALS):
        subset = [r for r in rows if r["benchmark"] == benchmark and r["elapsed_seconds"]]
        for mode in PERFORMANCE_MODES:
            points = []
            for k in PERFORMANCE_K:
                values = [float(r["elapsed_seconds"]) for r in subset if r["heuristics"] == mode and int(r["K"]) == k and r["verdict"] not in ("ERROR", "TIMEOUT", "UNKNOWN", "UNSUPPORTED")]
                if values:
                    points.append((k, statistics.median(values)))
            if points:
                ax.plot([x for x, _ in points], [y for _, y in points], marker="o", label=mode)
        ax.set_title(benchmark)
        ax.set_xlabel("K")
        ax.grid(True, alpha=0.25)
    axes[0].set_ylabel("Verifier time (seconds)")
    axes[-1].legend(frameon=False, fontsize=8)
    fig.tight_layout()
    fig.savefig(GRAPHS / "performance_runtime_vs_K.png", dpi=180)
    plt.close(fig)


def completeness_graphs(rows):
    GRAPHS.mkdir(parents=True, exist_ok=True)
    benchmarks = sorted({r["benchmark"] for r in rows if r["case_kind"] == "mutant"})
    # Technical failures and UNKNOWN results are excluded from the kill-rate denominator.
    fig, ax = plt.subplots(figsize=(7, 4))
    for benchmark in benchmarks:
        points = []
        subset = [r for r in rows if r["benchmark"] == benchmark and r["case_kind"] == "mutant"]
        for n in MUTANT_N:
            tested = [r for r in subset if int(r["N"]) == n and r["verdict"] in ("ACCEPT", "REJECT")]
            if tested:
                points.append((n, sum(r["verdict"] == "REJECT" for r in tested) / len(tested)))
        if points:
            ax.plot([x for x, _ in points], [y for _, y in points], marker="o", label=benchmark)
    ax.set(xlabel="N", ylabel="Mutant kill rate", ylim=(0, 1))
    ax.grid(True, alpha=0.25)
    ax.legend(frameon=False, fontsize=8)
    fig.tight_layout()
    fig.savefig(GRAPHS / "completeness_kill_rate_vs_N.png", dpi=180)
    plt.close(fig)

    fig, ax = plt.subplots(figsize=(7, 4))
    for benchmark in benchmarks:
        points = []
        subset = [r for r in rows if r["benchmark"] == benchmark and r["case_kind"] == "mutant"]
        for n in MUTANT_N:
            times = [float(r["elapsed_seconds"]) for r in subset if int(r["N"]) == n and r["verdict"] == "REJECT" and r["elapsed_seconds"]]
            if times:
                points.append((n, statistics.median(times)))
        if points:
            ax.plot([x for x, _ in points], [y for _, y in points], marker="o", label=benchmark)
    ax.set(xlabel="N", ylabel="Median time for killed mutants (seconds)")
    ax.grid(True, alpha=0.25)
    ax.legend(frameon=False, fontsize=8)
    fig.tight_layout()
    fig.savefig(GRAPHS / "completeness_time_to_kill_vs_N.png", dpi=180)
    plt.close(fig)

def run_performance(exe, originals):
    path = OUT / "appendix_performance.csv"
    reset_csv(path)
    rows = []
    total = len(originals) * len(PERFORMANCE_K) * len(PERFORMANCE_MODES) * PERFORMANCE_REPEATS
    done = 0
    print(f"\nPerformance: N={PERFORMANCE_N}, K={PERFORMANCE_K}, modes={PERFORMANCE_MODES}")
    for benchmark, file in originals.items():
        for k in PERFORMANCE_K:
            for mode in PERFORMANCE_MODES:
                for _ in range(PERFORMANCE_REPEATS):
                    row = run_case(
                        exe, "performance", benchmark, "original", file,
                        PERFORMANCE_N, k, mode, PERFORMANCE_INVARIANT_TIMEOUT_MS,
                        PERFORMANCE_TIMEOUT_SECONDS,
                    )
                    rows.append(row)
                    append_csv(path, row)
                    done += 1
                    print(f"[{done}/{total}] {benchmark}, K={k}, {mode}: {row['verdict']}, " f"{row['elapsed_seconds'] or row['wall_seconds']}s")
    performance_graph(rows)
    print(f"Saved {path} and {GRAPHS / 'performance_runtime_vs_K.png'}")
    return rows


def run_completeness(exe, invalids, mutants):
    path = OUT / "appendix_completeness.csv"
    reset_csv(path)
    rows = []
    cases = [(name, "invalid_control", file) for name, file in invalids.items()]
    cases += [(name, "mutant", file) for name, files in mutants.items() for file in files]
    tasks = [
        (n, benchmark, kind, file, K_BY_BENCHMARK.get(benchmark, DEFAULT_K))
        for n in MUTANT_N
        for benchmark, kind, file in cases
    ]
    total = len(tasks)
    print(
        f"\nCompleteness: N={MUTANT_N.start}..{MUTANT_N.stop - 1}, "
        f"mode={COMPLETENESS_MODE}, {len(cases)} files, {MAX_WORKERS} workers, "
        f"timeout={COMPLETENESS_TIMEOUT_SECONDS}s"
    )

    # Each case launches its own verifier process. The main thread alone writes the CSV.
    # Parallelizing this large experiment saves wall time without racing on output files.
    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as pool:
        futures = {
            pool.submit(
                run_case, exe, "completeness", benchmark, kind, file, n, k,
                COMPLETENESS_MODE, COMPLETENESS_INVARIANT_TIMEOUT_MS,
                COMPLETENESS_TIMEOUT_SECONDS,
            ): (n, benchmark, kind, file)
            for n, benchmark, kind, file, k in tasks
        }
        for done, future in enumerate(as_completed(futures), start=1):
            n, benchmark, kind, file = futures[future]
            try:
                row = future.result()
            except Exception as exc:
                row = failed_row(
                    "completeness", benchmark, kind, file, n,
                    K_BY_BENCHMARK.get(benchmark, DEFAULT_K), COMPLETENESS_MODE,
                    "ERROR", 0.0, str(exc),
                )
            rows.append(row)
            append_csv(path, row)
            if kind == "mutant":
                outcome = "KILLED" if row["kill"] == "true" else row["verdict"]
            else:
                outcome = f"invalid control: {row['verdict']}"
            print(f"[{done}/{total}] N={n}: {outcome} — {file.name}")

    completeness_graphs(rows)
    print(f"Saved {path} and two completeness graphs in {GRAPHS}")
    return rows


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    GRAPHS.mkdir(parents=True, exist_ok=True)
    missing = [str(p) for p in ORIGINALS.values() if not p.is_file()]
    if missing:
        raise FileNotFoundError("Missing required benchmarks:\n" + "\n".join(missing))
    invalids, mutants = find_invalids(), find_mutants()
    print(f"Project: {ROOT}")
    print(f"Mutant files: {sum(map(len, mutants.values()))}; invalid controls found: {len(invalids)}")
    print("CSV keeps runtime, inspected/pruned paths, generated/verified paths, and WLP size.")
    print("Install graph dependency if needed: python -m pip install matplotlib")
    exe = build_main()
    all_rows = []
    if RUN_PERFORMANCE_EXPERIMENT:
        all_rows += run_performance(exe, ORIGINALS)
    else:
        print("Skipping performance experiment (RUN_PERFORMANCE_EXPERIMENT=False).")
    all_rows += run_completeness(exe, invalids, mutants)
    errors = [r for r in all_rows if r["run_status"] in ("error", "timeout", "unsupported", "inconclusive", "unexpected_result")]
    controls = [r for r in all_rows if r["case_kind"] == "invalid_control"]
    control_failures = sum(r["run_status"] != "completed" for r in controls)
    print(f"\nDone. Results: {OUT}")
    print(f"Invalid controls not correctly rejected: {control_failures}/{len(controls)}")
    print(f"Errors, timeouts, unsupported, inconclusive, or unexpected results: {len(errors)}")
    return 1 if errors else 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
