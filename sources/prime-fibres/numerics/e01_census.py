#!/usr/bin/env python3
"""Exact rootless-quartic prime census. All artifacts stay alongside this file.

Examples:
 python3 -B numerics/e01_census.py --d 4 --primes all --bound 200
 python3 -B numerics/e01_census.py --d 5 --primes 2,3,7,11 --timeout 180
Each subprocess is watched at 0.1 s and killed at 7 GiB RSS (8 GiB task ceiling).
RSS sampling uses the platform-specific helper for owned child processes.
No other process is killed.
The base chart is a_0=b_0=1. Its length is NOT the whole projective length.
"""

# Locate dependencies relative to the public repository root.
from pathlib import Path as _EvidencePath
import sys as _evidence_sys
_evidence_sys.dont_write_bytecode = True
if not __debug__:
    raise RuntimeError("Python optimization disables certificate assertions")
_evidence_root = next(p for p in _EvidencePath(__file__).resolve().parents
                      if (p / "replay" / "portable.py").is_file())
_evidence_sys.path.insert(0, str(_evidence_root / "replay"))
from portable import public_root, executable, resident_bytes
import argparse
import ctypes
import hashlib
import json
import os
from pathlib import Path
import platform
import resource
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
SEED = 20261031


def coefficients(d, a0=0, b0=0):
    av = lambda i: "1" if i % d == a0 else f"a{i % d}"
    bv = lambda i: "1" if i % d == b0 else f"b{i % d}"
    C = lambda r, s: "+".join(
        f"{av(i)}*{bv(i+r)}*{bv(i+s)}*{av(i+r+s)}" for i in range(d))
    seen, gens = set(), []
    for r in range(d):
        for s in range(d):
            key = min((r,s), (s,r), (-r % d,-s % d), (-s % d,-r % d))
            if key in seen:
                continue
            seen.add(key)
            c = int(r == 0) + int(s == 0)
            gens.append("("+C(r,s)+")" + (f"-{c}*t" if c else ""))
    N = "+".join(f"{av(i)}*{bv(i)}" for i in range(d))
    names = ["y", "t"] + [f"b{i}" for i in range(d) if i != b0] + [f"a{i}" for i in range(d) if i != a0]
    return names, gens, N


def source(d, p, a0=0, b0=0, reduced=False, extras=()):
    names, gens, N = coefficients(d, a0, b0)
    eqs = gens + ["t*y-1"] + list(extras)
    if reduced:
        eqs += [N]
    return f'''ring r={p},({','.join(names)}),dp;
option(redSB);
ideal I={','.join(eqs)};
ideal G=slimgb(I);
G=std(G);
"RESULT dim",dim(G);
"RESULT length",vdim(G);
poly N={N};
"RESULT N2_in_ideal",reduce(N^2-{d+1}*t,G);
ideal H=std(G+ideal(N));
"RESULT dim_mod_N",dim(H);
"RESULT length_mod_N",vdim(H);
"RESULT DONE";
quit;
'''


def process_resident_bytes(pid):
    return resident_bytes(pid)

def run_job(d, p, timeout=180, a0=0, b0=0, reduced=False, extras=(), suffix="", reuse=True,
            custom_source=None, prefix="e01"):
    stem = f"{prefix}_d{d}_p{p}_a{a0}b{b0}" + ("_N" if reduced else "") + suffix
    path = HERE / stem
    inp = custom_source if custom_source is not None else source(d,p,a0,b0,reduced,extras)
    digest = hashlib.sha256(inp.encode()).hexdigest()
    meta_path = path.with_suffix(".json")
    if reuse and meta_path.exists():
        old = json.loads(meta_path.read_text())
        if old.get("status") == "complete" and old.get("input_sha256") == digest:
            return old
    path.with_suffix(".sing").write_text(inp)
    command = ["Singular", "-q", "--no-rc", f"--random={SEED}"]
    t0 = time.monotonic()
    with path.with_suffix(".sing").open() as fin, path.with_suffix(".out").open("w") as fout:
        proc = subprocess.Popen(command, stdin=fin, stdout=fout, stderr=subprocess.STDOUT,
                                cwd=HERE)
        print(f"START d={d} p={p} chart=a{a0}b{b0} N={reduced} pid={proc.pid}", flush=True)
        status = "running"
        while True:
            pid, state, usage = os.wait4(proc.pid, os.WNOHANG)
            if pid:
                proc.returncode = os.waitstatus_to_exitcode(state)
                status = "complete" if proc.returncode == 0 else "error"
                break
            over_memory = process_resident_bytes(proc.pid) > 7*1024**3
            cancelled = path.with_suffix('.cancel').exists()
            if time.monotonic()-t0 > timeout or over_memory or cancelled:
                # Exactly the child PID created above. No process-name matches.
                proc.kill()
                pid, state, usage = os.wait4(proc.pid, 0)
                proc.returncode = os.waitstatus_to_exitcode(state)
                status = "cancelled" if cancelled else ("memory_limit" if over_memory else "timeout")
                break
            time.sleep(0.1)
    raw = path.with_suffix(".out").read_text()
    values = {}
    for line in raw.splitlines():
        if line.startswith("RESULT "):
            pieces = line.split(maxsplit=2)
            if len(pieces) == 3:
                key, value = pieces[1:]
                try:
                    value = int(value)
                except ValueError:
                    pass
                values[key] = value
    if status == "complete" and ("RESULT DONE" not in raw or "?" in raw):
        status = "parse_error"
    result = dict(d=d,p=p,chart=[a0,b0],trace_quotient=reduced,extras=list(extras),
                  status=status,elapsed_s=round(time.monotonic()-t0,3),
                  peak_rss_bytes=usage.ru_maxrss if sys.platform=="darwin" else usage.ru_maxrss*1024,
                  memory_watchdog_bytes=7*1024**3,memory_task_ceiling_bytes=8*1024**3,
                  python=platform.python_version(),
                  seed=SEED,exact_field=f"F_{p}" if p else "Q",pid=proc.pid,
                  command=command,input_sha256=digest,returncode=proc.returncode,
                  result=values)
    meta_path.write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n")
    print("FINISH "+json.dumps(result,ensure_ascii=False),flush=True)
    return result


def primes_upto(n):
    return [p for p in range(2,n+1) if all(p%q for q in range(2,int(p**0.5)+1))]


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--d",type=int,required=True)
    ap.add_argument("--primes",default="all")
    ap.add_argument("--bound",type=int,default=200)
    ap.add_argument("--timeout",type=int,default=180)
    ap.add_argument("--a0",type=int,default=0)
    ap.add_argument("--b0",type=int,default=0)
    ap.add_argument("--trace",action="store_true")
    args=ap.parse_args()
    ps=primes_upto(args.bound) if args.primes=="all" else list(map(int,args.primes.split(',')))
    ps=[p for p in ps if not p or args.d%p]
    # Prioritize all requested arithmetic exceptional candidates.
    M=args.d*(args.d-1)*(args.d+1)*(args.d-2)*(args.d-3)
    ps.sort(key=lambda p:(bool(p and M%p),p))
    results=[]
    for p in ps:
        results.append(run_job(args.d,p,args.timeout,args.a0,args.b0,args.trace))
    summary=HERE/f"e01_census_d{args.d}_a{args.a0}b{args.b0}{'_N' if args.trace else ''}.json"
    summary.write_text(json.dumps(results,indent=2,ensure_ascii=False)+"\n")


if __name__=="__main__":
    main()
