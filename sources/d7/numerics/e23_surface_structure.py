#!/usr/bin/env python3.14
"""Inspect the exact linear part of the d6 surface face. No d7 work."""

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
from collections import Counter
from fractions import Fraction
import json
import sys
sys.dont_write_bytecode=True
from e10_face_system import build_chart,face_at,generic_square,row_reduce,SEED


def main():
    p=30241
    chart=build_chart(6,0,1,p)
    face=face_at(chart,list(map(Fraction,'1/2,1,0,1/2,1,1/2,1,1/2,0,1'.split(','))))
    rows=generic_square(face)
    high=[chart.names.index(s) for s in ['a2','a5','b2','b5']]
    subset=lambda f:{e:c for e,c in f.items() if any(e[j] for j in high)}
    out=dict(seed=SEED,p=p,names=chart.names,face_support=len(face.support),
             qface_rank=len(row_reduce(list(face.forms),p)),r_monomials=len(face.r_monomials),
             high_names=[chart.names[j] for j in high],
             high_monomials=len(set().union(*(subset(f).keys() for f in rows))),
             high_coeff_rank=len(row_reduce([subset(f) for f in rows],p)),
             high_terms={chart.names[j]:[list(e) for e in face.support if e[j]] for j in high})
    print(json.dumps(out,indent=2))


if __name__=='__main__':main()
