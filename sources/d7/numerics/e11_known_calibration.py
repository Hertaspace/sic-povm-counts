#!/usr/bin/env python3.14
"""Calibrate direct initial counting on published-in-repo d=4,5,6 weights.

Known weights are regression checks only.  The independent e20+ grid-free
vertex enumeration supplies the completeness check and must pass separately.
One Singular subprocess at a time. Fixed integer coefficient seed 20261102.
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
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import shutil
import sys
import time
sys.dont_write_bytecode = True
from e10_face_system import SEED, build_chart, count_face, face_at

CASES = {
    "d4_point16": dict(d=4,c=0,s=1,zero_names=[],
        w="1/2,1,1/2,1/2,1/2,1", expected=16),
    "d5_point64": dict(d=5,c=0,s=1,zero_names=[],
        w="1/2,1,1/4,3/4,1/2,3/4,1/4,1", expected=64),
    "d5_point36": dict(d=5,c=0,s=1,zero_names=[],
        w="1/2,1,2/3,1/3,1/2,1/3,2/3,1", expected=36),
    "d5_line8": dict(d=5,c=0,s=1,zero_names=["b2"],
        w="1/2,1,1,1,1/2,0,1,1", expected=8),
    "d6_point256": dict(d=6,c=0,s=1,zero_names=[],
        w="1/2,1,3/4,1/2,1/4,1/2,1/4,1/2,3/4,1", expected=256),
    "d6_line32": dict(d=6,c=0,s=1,zero_names=["b2"],
        w="1/2,1,1,1,1/2,1/2,0,1/2,1,1", expected=32),
    "d6_lineA32": dict(d=6,c=0,s=2,zero_names=["a1"],
        w="0,1/2,1,1,1/2,1,1/2,1/2,1,1", expected=32),
    "d6_surface1920": dict(d=6,c=0,s=1,zero_names=["a3","b4"],
        w="1/2,1,0,1/2,1,1/2,1,1/2,0,1", expected=1920),
}


def environment():
    sv = subprocess.run([shutil.which("Singular") or "Singular","--no-rc","--version"], capture_output=True,text=True).stdout.splitlines()[0]
    import sympy
    return dict(python=sys.version,platform=platform.platform(),sympy=sympy.__version__,
                singular=sv,precision="exact finite fields and exact rational/cyclotomic coefficients",
                source_sha256={Path(__file__).name:hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                    "e10_face_system.py":hashlib.sha256(Path(__file__).with_name("e10_face_system.py").read_bytes()).hexdigest()})


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--case",action="append",choices=CASES)
    ap.add_argument("--prime",type=int,action="append")
    ap.add_argument("--timeout",type=float,default=600)
    ap.add_argument("--strategy",default="sat",choices=["sat","colon","rabinowitsch"])
    ap.add_argument("--algorithm",default="std",choices=["std","slimgb"])
    ap.add_argument("--no-reducedness",action="store_true")
    args = ap.parse_args()
    print(json.dumps(dict(environment=environment(),seed=SEED,known_weights_only=True,
                         grid_free_completeness="NOT established by this script")),flush=True)
    results=[]
    for name in args.case or CASES:
        case=CASES[name]
        for p in args.prime or [30241,31081]:
            print(json.dumps(dict(start=name,p=p)),flush=True)
            ans=count_face(case["d"],case["c"],case["s"],list(map(Fraction,case["w"].split(","))),p,
                  timeout=args.timeout,reducedness=not args.no_reducedness,
                  strategy=args.strategy,algorithm=args.algorithm)
            ans.update(name=name,expected=case["expected"],zero_names=case["zero_names"])
            ans["calibration_pass"]=(ans["status"]=="PASS" and ans["length"]==case["expected"]
                  and ans["dim"]==0 and (args.no_reducedness or ans["reduced"] is True))
            results.append(ans)
            print(json.dumps(ans,sort_keys=True),flush=True)
    passed=all(r["calibration_pass"] for r in results)
    print(json.dumps(dict(status="PASS" if passed else "FAIL_OR_INCOMPLETE",runs=len(results),
                         seed=SEED,known_weights_only=True)),flush=True)


if __name__=="__main__": main()
