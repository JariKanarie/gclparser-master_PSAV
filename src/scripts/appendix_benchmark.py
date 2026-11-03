#!/usr/bin/env python3
import csv
import os
import sys
import time
import statistics
import subprocess
import matplotlib.pyplot as plt
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

RUN_PERFORMANCE_EXPERIMENT = False
RUN_COMPLETENESS_EXPERIMENT = False
# Performance settings
PERFORMANCE_N = 10
PERFORMANCE_K = [10, 20, 30, 40, 50, 60]
SELECTED_HEURISTIC = "prune+invariants"
PERFORMANCE_MODES = ["none", "prune", "simplify", "invariants", SELECTED_HEURISTIC, "all"]
# PERFORMANCE_MODES = ["none", SELECTED_HEURISTIC, "all"]
PERFORMANCE_REPEATS = 1  # Use 3 for more stable final measurements.
MUTANT_N = range(2, 11)
COMPLETENESS_MODE = "all"
DEFAULT_K = 50
# these will take long
PERFORMANCE_TIMEOUT_SECONDS = 2000
PERFORMANCE_INVARIANT_TIMEOUT_MS = 1000
COMPLETENESS_TIMEOUT_SECONDS = 600
COMPLETENESS_INVARIANT_TIMEOUT_MS = 1000

MAX_WORKERS = min(4, os.cpu_count() or 1)
HERE = Path(__file__).absolute()
CWD = Path.cwd()
ROOT = CWD if (CWD / "GCLparser.cabal").is_file() else HERE.parents[2]

if not (ROOT / "GCLparser.cabal").is_file():
    raise SystemExit("Run this script from the project root, or place it in src/scripts/.")

BENCH = ROOT / "examples" / "GCL" / "benchmark"
MUTANTS = BENCH / "mutants"
OUT = ROOT / "results" / "appendix"
GRAPHS = OUT / "graphs"
PERFORMANCE_CSV = OUT / "appendix_performance.csv"
COMPLETENESS_CSV = OUT / "appendix_completeness.csv"
COLUMNS = [
    "experiment", "benchmark", "kind", "file", "N", "K", "heuristics", "expected_verdict", "verdict", "kill", "elapsed_time", "wall_seconds", "paths_inspected",
    "paths_pruned", "full_paths_generated", "paths_verified", "total_wlp_size", "max_depth", "invariant_status", "run_status", "detail"
]

def clean_path(path):
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)

def invalids():
    found = {}
    for name, x in INVALID_STEMS.items():
        for path in BENCH.rglob("*.gcl"):
            if MUTANTS not in path.parents and path.stem.lower() == x.lower():
                found[name] = path
                break
    return found

def mutants():
    found = {}
    if not MUTANTS.is_dir():
        raise FileNotFoundError(f"Mutant folder not found: {MUTANTS}")
    for path in sorted(MUTANTS.rglob("*.gcl")):
        x = path.relative_to(MUTANTS)
        name = x.parts[0] if len(x.parts) > 1 else path.stem.split("_")[0]
        found.setdefault(name, []).append(path)
    return found

def build():
    def execute(args):
        return subprocess.run(args, cwd=ROOT, text=True, capture_output=True)
    build = execute(["cabal", "build", "exe:Main"])
    if build.returncode:
        raise RuntimeError((build.stdout + "\n" + build.stderr)[-5000:])
    l = execute(["cabal", "list-bin", "exe:Main"])
    if l.returncode:
        raise RuntimeError((l.stdout + "\n" + l.stderr)[-3000:])
    exe = Path(l.stdout.strip().splitlines()[-1])
    if not exe.is_absolute():
        exe = ROOT / exe
    if not exe.is_file():
        raise FileNotFoundError(f"Cabal executable not found: {exe}")
    return exe

def parseResult(stdout):
    keys = ["benchmark", "file", "N", "K", "heuristics", "verdict", "elapsed_time", "paths_inspected", "paths_pruned", 
            "full_paths_generated", "paths_verified", "total_wlp_size", "depth_report", "invariant_status"]
    for l in stdout.splitlines():
        if l.startswith("BENCHMARK_RESULT\t"):
            v = l.split("\t")[1:]
            if len(v) == len(keys):
                result = dict(zip(keys, v))
                d = result.pop("depth_report")
                if result["verdict"] == "UNSUPPORTED":
                    result["max_depth"] = ""
                elif d.lower() == "k":
                    result["max_depth"] = "K_LIMIT"
                else:
                    result["max_depth"] = d
                return result
    return None


def run(exe, experiment, benchmark, kind, file, n, k, mode, invariant_timeout_ms, run_timeout_seconds):
    sTime = time.perf_counter()
    cmd = [str(exe), "--benchmark", "--file", str(file), "--k", str(k), "--n", str(n), "--heuristics", mode, "--invariant-timeout-ms", str(invariant_timeout_ms)]
    try:
        p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=run_timeout_seconds)
        r = parseResult(p.stdout)
        w = time.perf_counter() - sTime
        if r is None:
            out = (p.stdout or "") + "\n" + (p.stderr or "")
            errors = next((line.split("\t", 1)[1] for line in out.splitlines() if line.startswith("BENCHMARK_ERROR\t")), None)
            if errors:
                verdict, detail = "ERROR", errors[-1500:]
            elif w >= run_timeout_seconds * 0.95 or any(word in out.lower() for word in ("timeout", "timed out", "time limit exceeded")):
                verdict = "TIMEOUT"
                detail = f"No BENCHMARK_RESULT before the {run_timeout_seconds}s timeout limit"
            elif p.returncode == 0:
                verdict = "UNKNOWN"
                detail = "Process exited without a BENCHMARK_RESULT row; result is inconclusive"
            else:
                verdict = "ERROR"
                detail = (out.strip() or f"exit code {p.returncode}")[-1500:]
            return failed(experiment, benchmark, kind, file, n, k, mode, verdict, w, detail)
        verdict = r["verdict"]
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
        inv = r.get("invariant_status", "")
        elapsed_time = r.get("elapsed_time", "")
        return {
            "experiment": experiment, "benchmark": benchmark, "kind": kind,
            "file": clean_path(file), "N": n, "K": k, "heuristics": mode,
            "expected_verdict": expected, "verdict": verdict, "kill": str(killed).lower(),
            "elapsed_time": elapsed_time, "wall_seconds": f"{w:.3f}",
            "paths_inspected": r.get("paths_inspected", ""),
            "paths_pruned": r.get("paths_pruned", ""),
            "full_paths_generated": r.get("full_paths_generated", ""),
            "paths_verified": r.get("paths_verified", ""),
            "total_wlp_size": r.get("total_wlp_size", ""),
            "max_depth": r.get("max_depth", ""),
            "invariant_status": inv, "run_status": status, "detail": "",
        }
    except subprocess.TimeoutExpired:
        return failed(experiment, benchmark, kind, file, n, k, mode, "TIMEOUT", time.perf_counter() - sTime, f"Exceeded {run_timeout_seconds}s")
    except Exception as exc:
        return failed(experiment, benchmark, kind, file, n, k, mode, "ERROR", time.perf_counter() - sTime, str(exc))


def failed(experiment, benchmark, kind, file, n, k, mode, verdict, wall, detail):
    row = {key: "" for key in COLUMNS}
    expected = {"original": "ACCEPT", "invalid_control": "REJECT"}.get(kind, "NOT_KNOWN")
    row.update(experiment=experiment, benchmark=benchmark, kind=kind, file=clean_path(file), N=n, K=k, heuristics=mode, expected_verdict=expected, 
               verdict=verdict, kill="false", wall_seconds=f"{wall:.3f}", run_status=("inconclusive" if verdict == "UNKNOWN" else verdict.lower()), detail=detail)
    return row

def reset_csv(path):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as f:
        csv.DictWriter(f, fieldnames=COLUMNS).writeheader()

def append_csv(path, row):
    with path.open("a", newline="", encoding="utf-8") as f:
        csv.DictWriter(f, fieldnames=COLUMNS).writerow(row)

def performanceGraph(rows):
    GRAPHS.mkdir(parents=True, exist_ok=True)
    modes = ["none"] + [mode for mode in PERFORMANCE_MODES if mode != "none"]
    baseline_style = {"color": "black", "linestyle": "--", "alpha": 0.5, "linewidth": 2.0, "marker": "s", "zorder": 5}
    def save_graph(bench, s, modes, file, scale):
        fig, ax = plt.subplots(figsize=(7.2, 4.6))
        for mode in modes:
            points = []
            for k in PERFORMANCE_K:
                times = [
                    float(row["elapsed_time"]) for row in s
                    if row["heuristics"] == mode and int(row["K"]) == k
                    and row["verdict"] not in ("ERROR", "TIMEOUT", "UNKNOWN", "UNSUPPORTED")
                    and row["elapsed_time"] and float(row["elapsed_time"]) > 0
                ]
                if times:
                    points.append((k, statistics.median(times)))
            if points:
                style = baseline_style if mode == "none" else {}
                ax.plot(
                    [x for x, _ in points], [y for _, y in points],
                    marker=style.get("marker", "o"),
                    linestyle=style.get("linestyle", "-"),
                    linewidth=style.get("linewidth", 1.6),
                    color=style.get("color"),
                    alpha=style.get("alpha", 1.0),
                    zorder=style.get("zorder", 2),
                    label="none (baseline)" if mode == "none" else mode,
                )
        ax.set_title(bench)
        ax.set_xlabel("K (path-depth bound)")
        ax.set_ylabel("Time to verifier result (seconds)")
        ax.set_xticks(PERFORMANCE_K)
        if scale:
            ax.set_yscale("log")
        ax.grid(True, which="both" if scale else "major", alpha=0.25)
        ax.legend(frameon=False, fontsize=9)
        fig.tight_layout()
        fig.savefig(GRAPHS / file, dpi=200, bbox_inches="tight")
        plt.close(fig)

    for benchmark in ORIGINALS:
        subset = [row for row in rows if row["experiment"] == "performance" and row["benchmark"] == benchmark]
        save_graph(benchmark, subset, modes, f"performance_{benchmark}_runtime_vs_K.png", False)
        save_graph(benchmark, subset, modes, f"performance_{benchmark}_runtime_vs_K_log.png", True)
        for mode in modes:
            if mode == "none":
                continue
            name = mode.replace("+", "_")
            save_graph(benchmark, subset, ["none", mode], f"performance_{benchmark}_{name}_vs_none.png", False)
            save_graph(benchmark, subset, ["none", mode], f"performance_{benchmark}_{name}_vs_none_log.png", True)

    # # Remove obsolete combined charts from earlier versions.
    # for old_name in ("performance_runtime_vs_K.png", "performance_runtime_vs_K_log.png", "performance_success_vs_K.png", "performance_full_completion_time_vs_K.png"):
    #     old = GRAPHS / old_name
    #     if old.exists():
    #         old.unlink()

def performanceNoneBaselineGraph(rows):
    GRAPHS.mkdir(parents=True, exist_ok=True)
    benchmarks = ["bsort", "divByN", "memberOf"]
    fig, ax = plt.subplots(figsize=(8, 5))
    for benchmark in benchmarks:
        points = []
        for k in PERFORMANCE_K:
            times = [float(r["elapsed_time"]) for r in rows if r["experiment"] == "performance" and r["benchmark"] == benchmark and r["heuristics"] == "none" 
                     and int(r["K"]) == k and r["verdict"] in ("ACCEPT", "REJECT") and r.get("elapsed_time", "") and float(r["elapsed_time"]) > 0]
            if times:
                points.append((k, statistics.median(times)))
        if points:
            ax.plot([x for x, _ in points], [y for _, y in points], marker="o", label=f"{benchmark}.gcl")
    ax.set_xlabel("K")
    ax.set_ylabel("Verification time (seconds)")
    ax.set_title("Baseline performance (no heuristics)")
    ax.set_xticks(PERFORMANCE_K)
    ax.grid(True, alpha=0.3)
    ax.legend()
    fig.tight_layout()
    fig.savefig(GRAPHS / "performance_none_baseline.png", dpi=200)
    plt.close(fig)

def completenessGraphs(rows):
    GRAPHS.mkdir(parents=True, exist_ok=True)
    benchmarks = sorted({r["benchmark"] for r in rows if r["kind"] == "mutant"})
    fig, ax = plt.subplots(figsize=(7, 4))
    for benchmark in benchmarks:
        p = []
        s = [r for r in rows if r["benchmark"] == benchmark and r["kind"] == "mutant"]
        for n in MUTANT_N:
            tested = [r for r in s if int(r["N"]) == n and r["verdict"] in ("ACCEPT", "REJECT")]
            if tested:
                p.append((n, sum(r["verdict"] == "REJECT" for r in tested) / len(tested)))
        if p:
            ax.plot([x for x, _ in p], [y for _, y in p], marker="o", label=benchmark)
    ax.set(xlabel="N", ylabel="Mutant kill rate", ylim=(0, 1))
    ax.grid(True, alpha=0.25)
    ax.legend(frameon=False, fontsize=8)
    fig.tight_layout()
    fig.savefig(GRAPHS / "completeness_kill_rate_vs_N.png", dpi=180)
    plt.close(fig)
    fig, ax = plt.subplots(figsize=(7, 4))
    for benchmark in benchmarks:
        p = []
        s = [r for r in rows if r["benchmark"] == benchmark and r["kind"] == "mutant"]
        for n in MUTANT_N:
            times = [float(r["elapsed_time"]) for r in s if int(r["N"]) == n and r["verdict"] == "REJECT" and r["elapsed_time"]]
            if times:
                p.append((n, statistics.median(times)))
        if p:
            ax.plot([x for x, _ in p], [y for _, y in p], marker="o", label=benchmark)
    ax.set(xlabel="N", ylabel="Median time for killed mutants (seconds)")
    ax.grid(True, alpha=0.25)
    ax.legend(frameon=False, fontsize=8)
    fig.tight_layout()
    fig.savefig(GRAPHS / "completeness_time_to_kill_vs_N.png", dpi=180)
    plt.close(fig)


def runPerformance(exe, originals):
    reset_csv(PERFORMANCE_CSV)
    rows = []
    tot = len(originals) * len(PERFORMANCE_K) * len(PERFORMANCE_MODES) * PERFORMANCE_REPEATS
    done = 0
    print(f"\nPerformance: N={PERFORMANCE_N}, K={PERFORMANCE_K}, modes={PERFORMANCE_MODES}")
    for benchmark, file in originals.items():
        for k in PERFORMANCE_K:
            for mode in PERFORMANCE_MODES:
                for _ in range(PERFORMANCE_REPEATS):
                    row = run(
                        exe, "performance", benchmark, "original", file,
                        PERFORMANCE_N, k, mode, PERFORMANCE_INVARIANT_TIMEOUT_MS,
                        PERFORMANCE_TIMEOUT_SECONDS,
                    )
                    rows.append(row)
                    append_csv(PERFORMANCE_CSV, row)
                    done += 1
                    print(f"[{done}/{tot}] {benchmark}, N={PERFORMANCE_N}, K={k}, {mode}: {row['verdict']}, " f"accepted={row.get('accepted_at_K', '')}, " 
                          f"paths={row.get('paths_inspected', '')}, " f"full-complete={row.get('full_complete_accept', '')}, " f"time={row['elapsed_time'] or row['wall_seconds']}s")
    performanceGraph(rows)
    performanceNoneBaselineGraph(rows)
    print(f"Saved {PERFORMANCE_CSV} and runtime graph in {GRAPHS}")
    return rows


def runCompleteness(exe, invalids, mutants):
    reset_csv(COMPLETENESS_CSV)
    rows = []
    xs = [(name, "invalid_control", file) for name, file in invalids.items()]
    xs += [(name, "mutant", file) for name, files in mutants.items() for file in files]
    tasks = [(n, benchmark, kind, file, K_BY_BENCHMARK.get(benchmark, DEFAULT_K)) for n in MUTANT_N for benchmark, kind, file in xs]
    total = len(tasks)
    print(f"\nCompleteness: N={MUTANT_N.start}..{MUTANT_N.stop - 1}, " f"mode={COMPLETENESS_MODE}, {len(xs)} files, {MAX_WORKERS} workers, " f"timeout={COMPLETENESS_TIMEOUT_SECONDS}s")

    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as pool:
        futures = {
            pool.submit(
                run, exe, "completeness", benchmark, kind, file, n, k,
                COMPLETENESS_MODE, COMPLETENESS_INVARIANT_TIMEOUT_MS,
                COMPLETENESS_TIMEOUT_SECONDS,
            ): (n, benchmark, kind, file)
            for n, benchmark, kind, file, k in tasks
        }
        for done, future in enumerate(as_completed(futures), start=1):
            n, bench, kind, file = futures[future]
            try:
                row = future.result()
            except Exception as exc:
                row = failed("completeness", bench, kind, file, n, K_BY_BENCHMARK.get(bench, DEFAULT_K), COMPLETENESS_MODE, "ERROR", 0.0, str(exc))
            rows.append(row)
            append_csv(COMPLETENESS_CSV, row)
            if kind == "mutant":
                res = "KILLED" if row["kill"] == "true" else row["verdict"]
            else:
                res = f"invalid control: {row['verdict']}"
            print(f"[{done}/{total}] N={n}: {res}, {file.name}, benchmark={bench}, time={row['elapsed_time'] or row['wall_seconds']}s")

    completenessGraphs(rows)
    print(f"Saved {COMPLETENESS_CSV} and two completeness graphs in {GRAPHS}")
    return rows


def readCsvRows(path):
    if not path.is_file():
        print(f"Skipping missing CSV (no saved results): {path}")
        return []
    with path.open("r", newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f))


def reloadGraphs(performance_path, completeness_path):
    p_rows = readCsvRows(performance_path)
    c_rows = readCsvRows(completeness_path)
    if p_rows:
        performanceGraph(p_rows)
        performanceNoneBaselineGraph(p_rows)
    if c_rows:
        completenessGraphs(c_rows)
    if not p_rows and not c_rows:
        raise FileNotFoundError("No saved benchmark CSV rows found. Enable an experiment to create results, or place the appendix CSV files under results/appendix.")
    print(f"Reloaded graphs from saved CSV files into {GRAPHS}")


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    GRAPHS.mkdir(parents=True, exist_ok=True)
    missing = [str(p) for p in ORIGINALS.values() if not p.is_file()]
    if missing:
        raise FileNotFoundError("Missing required benchmarks:\n" + "\n".join(missing))
    print(f"Project: {ROOT}")
    print(f"Mutant files: {sum(map(len, mutants().values()))}; invalid controls found: {len(invalids())}")
    print("CSV records runtime, path/WLP statistics, acceptance at each K, and full-completion status/time.")
    print("Install graph dependency if needed: python -m pip install matplotlib")
    exe = build()
    all_rows = []
    
    if RUN_PERFORMANCE_EXPERIMENT:
        all_rows += runPerformance(exe, ORIGINALS)
    else:
        print("Skipping performance experiment (RUN_PERFORMANCE_EXPERIMENT=False).")

    if RUN_COMPLETENESS_EXPERIMENT:
        all_rows += runCompleteness(exe, invalids(), mutants())
    else:
        print("Skipping completeness experiment (RUN_COMPLETENESS_EXPERIMENT=False).")

    if not (RUN_PERFORMANCE_EXPERIMENT or RUN_COMPLETENESS_EXPERIMENT):
        print("reloading graphs from CSV files to ensure they are up to date.")
        reloadGraphs(PERFORMANCE_CSV, COMPLETENESS_CSV)
    actual_errors = [r for r in all_rows if r["run_status"] == "error"]
    unexpected = [r for r in all_rows if r["run_status"] == "unexpected_result"]
    timeouts = [r for r in all_rows if r["run_status"] == "timeout"]
    inconclusive = [r for r in all_rows if r["run_status"] == "inconclusive"]
    unsupported = [r for r in all_rows if r["run_status"] == "unsupported"]
    controls = [r for r in all_rows if r["kind"] == "invalid_control"]
    control_failures = sum(r["run_status"] != "completed" for r in controls)
    print(f"\nDone. Results: {OUT}")
    print(f"Invalid controls not correctly rejected: {control_failures}/{len(controls)}")
    print(f"Timeouts: {len(timeouts)}; inconclusive/unknown: {len(inconclusive)}; " f"unsupported: {len(unsupported)}; "
        f"unexpected results: {len(unexpected)}; " f"actual errors: {len(actual_errors)}")

    return 1 if actual_errors or unexpected else 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
