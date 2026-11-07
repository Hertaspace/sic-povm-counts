#!/usr/bin/env python3
"""Compute the trace-zero section first, without expensive full-fibre GB.

Together with N^2 in I, reduced trace-zero section and exact Jacobian ranks
certify each full local algebra, so this does not presume a flat model.
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
from pathlib import Path
import subprocess, sys, time, platform
from e01_fibre import program, ROOT

d,p=map(int,sys.argv[1:3]); timeout=int(sys.argv[3]) if len(sys.argv)>3 else 600
stem=ROOT/'numerics'/f'e04_d{d}_p{p}'
code=program(d,p,True).replace('ideal G=std(I);','ideal G=I;').replace('"FULL_DIM",dim(G); "FULL_LENGTH",vdim(G);','').replace('"TRACE_SQUARE_REMAINDER",reduce(N^2-('+str(d+1)+')*t,G);','')
stem.with_suffix('.sing').write_text(code)
start=time.monotonic()
print(f'Python={platform.python_version()} d={d} p={p} seed=20261031 exact=Fp timeout={timeout}',flush=True)
proc=subprocess.Popen(['Singular','-q'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
stem.with_suffix('.pid').write_text(str(proc.pid))
try:
    stdout,stderr=proc.communicate(code,timeout=timeout)
    stem.with_suffix('.singular.out').write_text(stdout+stderr)
    print(stdout);print(stderr);print(f'elapsed={time.monotonic()-start:.3f} returncode={proc.returncode}')
except subprocess.TimeoutExpired:
    proc.kill(); stdout,stderr=proc.communicate()
    stem.with_suffix('.singular.out').write_text(stdout+stderr+'\nTIMEOUT\n')
    print(stdout);print(stderr);print(f'TIMEOUT elapsed={time.monotonic()-start:.3f}')
