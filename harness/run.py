"""Run fresh, deterministic searches and audit their claims, one process at a time."""
import argparse
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
from time import perf_counter

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean-qutrit"
PROBLEMS = ("quantum", "shannon", "euler")
AXIOMS = "[propext, Classical.choice, Quot.sound]"


def run_command(args, directory=ROOT):
    start = perf_counter()
    env = dict(os.environ, LEAN_NUM_THREADS="1", OMP_NUM_THREADS="1", OPENBLAS_NUM_THREADS="1")
    env.pop("PYTHONOPTIMIZE", None)
    process = subprocess.run(args, cwd=directory, env=env, capture_output=True, text=True)
    output = (process.stdout + process.stderr).strip()
    if process.returncode:
        raise RuntimeError(f"{' '.join(map(str,args))} exited {process.returncode}\n{output}")
    return {"seconds": round(perf_counter() - start, 3), "output": output}


def python(script, *args):
    return run_command([sys.executable, "-B", script, *args])


def search(problem, options):
    if problem == "quantum":
        result = python("lean-qutrit/Qmds/search_rays.py", "--start", str(options.start_scale), "--stop", str(options.stop_scale))
        kind = "bounded exclusion" if "no zero-free" in result["output"] else "polynomial candidate"
    elif problem == "shannon":
        result = python("shannon-seven/search_exchanges.py", "--removed", str(options.shannon_removed))
        kind = "bounded exclusion" if "No improving exchange" in result["output"] else "candidate code"
    else:
        result = python("euler-sixth/search_one_pair.py", str(options.euler_bound))
        kind = "bounded exclusion" if result["output"].endswith("witness=None") else "candidate identity"
    return {"status": kind, **result}


def verify(problem):
    if problem == "shannon":
        result = python("shannon-seven/search_exchanges.py", "--removed", "4")
        if "Verified 368-word witness:" in result["output"]:
            return {"status": "368-word witness passed all pair checks", "steps": [result]}
        if result["output"].splitlines() != ["Connected deletion sets tested by size: [8, 244, 1984, 12387]",
                                             "No improving exchange in the tested neighborhood."]:
            raise ValueError(f"Unrecognized exchange result: {result}")
        return {"status": "known finite exclusion reproduced on the published seed", "steps": [result]}
    if problem == "euler":
        result = python("euler-sixth/check_one_pair.py", "500000")
        if result["output"] != "direct lookup through 500000: 711 eligible pairs, 2329 complementary searches, witness=None":
            raise ValueError(f"Independent search differs from the recorded exclusion: {result}")
        return {"status": "finite exclusion cross-checked by direct lookup", "steps": [result]}

    binary = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    data = python("lean-qutrit/Qmds/search_rays.py", "--check-file", "lean-qutrit/Qmds/Order29Data.lean")
    concrete = python("lean-qutrit/Qmds/check_order29.py")
    build = run_command([binary, "build", "Qmds"], LEAN)
    audit = run_command([binary, "env", "lean", "Qmds.lean"], LEAN)
    for name in ("full_length_family", "full_length_16384"):
        required = f"'Qmds.Order29.{name}' depends on axioms: {AXIOMS}"
        if required not in audit["output"].splitlines():
            raise ValueError(f"Missing axiom audit line: {required}")
    return {"status": "Lean-checked family and independently enumerated first case",
            "steps": [data, concrete, build, audit]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("search", "verify", "all"))
    parser.add_argument("--problem", action="append", choices=PROBLEMS)
    parser.add_argument("--json", action="store_true", help="emit a machine-readable report")
    parser.add_argument("--start-scale", type=int, default=1, help="first quantum scale to search")
    parser.add_argument("--stop-scale", type=int, default=16383, help="last quantum scale to search")
    parser.add_argument("--shannon-removed", type=int, choices=range(1,6), default=4)
    parser.add_argument("--euler-bound", type=int, default=500000, help="largest right-hand base")
    args = parser.parse_args()
    if not 1 <= args.start_scale <= args.stop_scale <= 16383 or args.euler_bound < 1:
        parser.error("invalid search interval")
    if args.mode != "search" and (args.start_scale, args.stop_scale, args.shannon_removed, args.euler_bound) != (1,16383,4,500000):
        parser.error("custom bounds apply to search mode; verify and all audit the recorded claims")
    report = {"python": platform.python_version(), "platform": platform.platform(), "runs": []}
    failed = False
    for problem in dict.fromkeys(args.problem or PROBLEMS):
        for phase in (("search", "verify") if args.mode == "all" else (args.mode,)):
            row = {"problem": problem, "phase": phase}
            start = perf_counter()
            try:
                row.update(search(problem, args) if phase == "search" else verify(problem))
            except (OSError, ValueError, RuntimeError) as err:
                row.update(status="failed", error=str(err))
                failed = True
            row["seconds"] = round(perf_counter() - start, 3)
            report["runs"].append(row)
            if not args.json:
                print(f"{problem} {phase} | {row['seconds']:.3f}s | {row['status']}", flush=True)
                if "output" in row or "error" in row:
                    print(row.get("output", row.get("error")), flush=True)
    if args.json:
        print(json.dumps(report, indent=2))
    return int(failed)


if __name__ == "__main__":
    sys.exit(main())
