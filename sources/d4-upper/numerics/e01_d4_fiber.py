#!/usr/bin/env python3
"""Exact d=4, p=5 equal-overlap fiber and chart-complement certificate.

Python stdlib + Singular. All generated input/output stays beside this script.
The complement tests have no projective normalization: t*y=1 already forces
both a and b nonzero. Thus a unit ideal certifies geometric chart coverage.
Seed is fixed; arithmetic is exact in GF(625), with native primitive w.
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
import json
import os
from pathlib import Path
import platform
import random
import subprocess
import time

ROOT = Path(__file__).resolve().parent


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20261031)
    ap.add_argument("--timeout", type=int, default=180)
    ap.add_argument("--complements", action="store_true")
    args = ap.parse_args()
    rng = random.Random(args.seed)
    d, q = 4, 625
    aa = ",".join(f"a{i}" for i in range(d))
    bb = ",".join(f"b{i}" for i in range(d))
    la = "+".join(f"w^{rng.randrange(1,q-1)}*a{i}" for i in range(d))
    lb = "+".join(f"w^{rng.randrange(1,q-1)}*b{i}" for i in range(d))
    seen, reps = set(), []
    for x in range(d):
        for z in range(d):
            p, m = (x, z), ((-x) % d, (-z) % d)
            if p == (0, 0) or p in seen:
                continue
            seen.update((p, m))
            reps.append(p)
    equations = ",".join(f"Zf({x},{z})*Zf({-x},{-z})-t" for x,z in reps)
    body = f"""ring r=({q},w),(y,t,{bb},{aa}),dp;
number tau=w^78;
proc T(int k) {{ k=k mod 8; if(k<0){{k=k+8;}} return(tau^k); }}
proc Zf(int p1,int p2) {{
 poly z=0; int s; int bi;
 for(s=0;s<4;s++){{ bi=(s+p1) mod 4; if(bi<0){{bi=bi+4;}}
 z=z+T(p1*p2+2*p2*s)*var(3+bi)*var(7+s); }}
 return(z);
}}
option(redSB);
ideal J={equations},t*y-1;
poly la={la}; poly lb={lb};
ideal I=J,la-1,lb-1;
ideal G=std(I);
print("CHART_DIM="+string(dim(G)));
print("CHART_LENGTH="+string(vdim(G)));
print("TRACE_RELATION_REMAINDER="+string(reduce(Zf(0,0)^2,G)));
ideal H=std(G+ideal(Zf(0,0)));
print("TRACE_ZERO_LENGTH="+string(vdim(H)));
ideal E=finduni(H);
int i; poly f; poly gg; int sf=1;
for(i=1;i<=ncols(E);i++){{f=E[i];
 if(deg(f)>0){{gg=gcd(f,diff(f,var(i))); if(deg(gg)>0){{sf=0;}}}}
}}
print("TRACE_ZERO_REDUCED="+string(sf));
"""
    if args.complements:
        body += """ideal HA=std(J+ideal(la));
print("A_COMPLEMENT_UNIT="+string(reduce(1,HA)==0));
ideal HB=std(J+ideal(lb));
print("B_COMPLEMENT_UNIT="+string(reduce(1,HB)==0));
"""
    body += "quit;\n"
    inp = ROOT / "e01_d4_fiber.sing"
    inp.write_text(body)
    started = time.monotonic()
    env = dict(os.environ, OMP_NUM_THREADS="1", OPENBLAS_NUM_THREADS="1")
    # Singular is our own subprocess; subprocess.run timeout terminates this PID.
    try:
        command = ["Singular", "-q", "--no-rc", f"--random={args.seed}",
                   "--cpus=1", "--threads=1", "--flint-threads=1", str(inp)]
        result = subprocess.run(command, text=True,
                                capture_output=True, timeout=args.timeout, env=env)
        output = result.stdout
        metadata = dict(seed=args.seed, d=d, q=q, python=platform.python_version(),
                        exact=True, seconds=round(time.monotonic()-started,3),
                        returncode=result.returncode, complements=args.complements,
                        singular="4.4.1", command=command)
        print(json.dumps(metadata, sort_keys=True), flush=True)
        print(output, end="", flush=True)
        print(result.stderr, end="", flush=True)
        if result.returncode or "?" in output:
            raise SystemExit("Singular error: inspect output")
    except subprocess.TimeoutExpired as err:
        print(json.dumps(dict(seed=args.seed,d=d,q=q,timeout=args.timeout)), flush=True)
        for item in (err.stdout, err.stderr):
            if item:
                print(item.decode() if isinstance(item,bytes) else item, end="",flush=True)
        raise SystemExit("timeout")


if __name__ == "__main__":
    main()
