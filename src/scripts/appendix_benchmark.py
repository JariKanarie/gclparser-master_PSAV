#!/usr/bin/env python3
import csv
import os
import sys
import statistics
import subprocess
import matplotlib.pyplot as plt
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

RUN_PERFORMANCE_EXPERIMENT = True
RUN_COMPLETENESS_EXPERIMENT = True
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
K_BY_BENCHMARK = {name: DEFAULT_K for name in ("memberOf", "divByN", "pullUp", "bsort", "find12", "min")}
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
ORIGINALS = {name: BENCH / f"{name}.gcl" for name in ("memberOf", "divByN", "pullUp")}
INVALID_STEMS = {name: f"invalid{name[0].upper()}{name[1:]}" for name in ("memberOf", "divByN", "pullUp", "bsort", "find12", "min")}
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
    startTime = timeDOne.perf_counter()
    cmd = [str(exe), "--benchmark", "--file", str(file), "--k", str(k), "--n", str(n), "--heuristics", mode, "--invariant-timeout-ms", str(invariant_timeout_ms)]
    try:
        p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=run_timeout_seconds)
        r = parseResult(p.stdout)
        w = timeDOne.perf_counter() - startTime
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
        timeDOne = r.get("elapsed_time", "")
        return {
            "experiment": experiment, "benchmark": benchmark, "case_kind": kind,
            "file": clean_path(file), "N": n, "K": k, "heuristics": mode,
            "expected_verdict": expected, "verdict": verdict, "kill": str(killed).lower(),
            "elapsed_time": timeDOne, "wall_seconds": f"{w:.3f}",
            "paths_inspected": r.get("paths_inspected", ""),
            "paths_pruned": r.get("paths_pruned", ""),
            "full_paths_generated": r.get("full_paths_generated", ""),
            "paths_verified": r.get("paths_verified", ""),
            "total_wlp_size": r.get("total_wlp_size", ""),
            "max_depth": r.get("max_depth", ""),
            "invariant_status": inv, "run_status": status, "detail": "",
        }
    except subprocess.TimeoutExpired:
        return failed(experiment, benchmark, kind, file, n, k, mode, "TIMEOUT", timeDOne.perf_counter() - startTime, f"Exceeded {run_timeout_seconds}s")
    except Exception as exc:
        return failed(experiment, benchmark, kind, file, n, k, mode, "ERROR", timeDOne.perf_counter() - startTime, str(exc))


def failed(experiment, benchmark, kind, file, n, k, mode, verdict, wall, detail):
    row = {key: "" for key in COLUMNS}
    expected = {"original": "ACCEPT", "invalid_control": "REJECT"}.get(kind, "NOT_KNOWN")
    row.update(experiment=experiment, benchmark=benchmark, case_kind=kind, file=clean_path(file), N=n, K=k, heuristics=mode, expected_verdict=expected, 
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
    f, a = plt.subplots(1, len(ORIGINALS), figsize=(12.5, 4.0), sharey=False)
    for ax, benchmark in zip(a, ORIGINALS):
        subset = [r for r in rows if r["experiment"] == "performance" and r["benchmark"] == benchmark]
        for m in PERFORMANCE_MODES:
            p = []
            for k in PERFORMANCE_K:
                values = [float(r["elapsed_time"]) for r in subset if r["heuristics"] == m and int(r["K"]) == k
                    and r.get("elapsed_time", "") and r["verdict"] not in ("ERROR", "TIMEOUT", "UNKNOWN", "UNSUPPORTED") and float(r["elapsed_time"]) > 0]
                if values:
                    p.append((k, statistics.median(values)))
            if p:
                ax.plot([x for x, _ in p], [y for _, y in p], marker="o", label=m)
        ax.set_title(benchmark)
        ax.set_xlabel("K")
        ax.set_xticks(PERFORMANCE_K)
        # ax.set_yscale("log")
        ax.grid(True, which="major", alpha=0.28)
    a[0].set_ylabel("Time to verifier result (s)")
    xs = {}
    for ax in a:
        handles, labels = ax.get_legend_handles_labels()
        for handle, label in zip(handles, labels):
            xs.setdefault(label, handle)
    if xs:
        f.legend(xs.values(), xs.keys(), loc="upper center", ncol=3, frameon=False, fontsize=8)
    f.tight_layout(rect=(0, 0, 1, 0.88))
    f.savefig(GRAPHS / "performance_runtime_vs_K.png", dpi=200)
    plt.close(f)

    for oldName in ("performance_success_vs_K.png", "performance_full_completion_time_vs_K.png"):
        old = GRAPHS / oldName
        if old.exists():
            old.unlink()


def completenessGraphs(rows):
    GRAPHS.mkdir(parents=True, exist_ok=True)
    benchmarks = sorted({r["benchmark"] for r in rows if r["case_kind"] == "mutant"})
    # Technical failures and UNKNOWN results are excluded from the kill-rate denominator.
    fig, ax = plt.subplots(figsize=(7, 4))
    for benchmark in benchmarks:
        p = []
        s = [r for r in rows if r["benchmark"] == benchmark and r["case_kind"] == "mutant"]
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
        s = [r for r in rows if r["benchmark"] == benchmark and r["case_kind"] == "mutant"]
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


# Reload graphs from CSV files without rerunning the experiments.
def reloadGraphs(performance_path, completeness_path):
    performance_rows = []
    with performance_path.open("r", newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            performance_rows.append(row)
    completeness_rows = []
    with completeness_path.open("r", newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            completeness_rows.append(row)
    performanceGraph(performance_rows)
    completenessGraphs(completeness_rows)
    print(f"Reloaded graphs from {performance_path} and {completeness_path} into {GRAPHS}")


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

    actual_errors = [r for r in all_rows if r["run_status"] == "error"]
    unexpected = [r for r in all_rows if r["run_status"] == "unexpected_result"]
    if not (RUN_PERFORMANCE_EXPERIMENT or RUN_COMPLETENESS_EXPERIMENT):
        print("reloading graphs from CSV files to ensure they are up to date.")
        reloadGraphs(PERFORMANCE_CSV, COMPLETENESS_CSV)
    else:
        timeouts = [r for r in all_rows if r["run_status"] == "timeout"]
        inconclusive = [r for r in all_rows if r["run_status"] == "inconclusive"]
        unsupported = [r for r in all_rows if r["run_status"] == "unsupported"]
        controls = [r for r in all_rows if r["case_kind"] == "invalid_control"]
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
