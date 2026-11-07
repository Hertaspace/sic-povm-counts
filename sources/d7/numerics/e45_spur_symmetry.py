#!/usr/bin/env python3.14
"""Exact q invariance and full projective Heisenberg-parity group identities.

The signed variable s=+/-1 denotes P^((1-s)/2). Every coefficient identity is
checked in Z[zeta]/Phi_d, using the homogeneous lift of the exact chart model.
Server only. No numerical roots, tolerances, or floating point.
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
import hashlib
import json
from pathlib import Path
import sys
import time
sys.dont_write_bytecode=True
from e10_face_system import build_chart

H=Path(__file__).resolve().parent


def homogeneous(chart,f):
    d=chart.d;out={}
    for local,coeff in f.items():
        full=[0]*(2*d)
        for index,power in zip(chart.keep,local):full[index]=power
        full[chart.c]=2-sum(local[:d-1])
        full[d+chart.s]=2-sum(local[d-1:])
        assert min(full)>=0 and sum(full[:d])==sum(full[d:])==2
        out[tuple(full)]=coeff
    assert len(out)==len(f)
    return out


def permute(f,d,action):
    out={}
    for e,c in f.items():
        x=[0]*(2*d)
        for side in range(2):
            for k in range(d):x[side*d+action(k)]=e[side*d+k]
        key=tuple(x)
        assert key not in out
        out[key]=c
    return out


def verify(d):
    start=time.monotonic();chart=build_chart(d,0,1)
    terms=0
    for f in chart.q:
        full=homogeneous(chart,f);terms+=len(full)
        assert permute(full,d,lambda k:(k-1)%d)==full,'X invariance failed'
        assert permute(full,d,lambda k:(-k)%d)==full,'parity invariance failed'
        for e in full:
            assert sum(k*(e[k]-e[d+k]) for k in range(d))%d==0,'Z character not trivial'
    # For U=X^i Z^j P^((1-s)/2), input basis index r is sent to
    # i+s*r with phase zeta^(j*s*r). Distinctness is projective: each
    # matrix is normalized by its input-index-zero coefficient, already 1.
    group=[(s,i,j) for s in (1,-1) for i in range(d) for j in range(d)]
    acts={}
    for s,i,j in group:
        permutation=tuple((i+s*r)%d for r in range(d))
        exponent=tuple((j*s*r)%d for r in range(d))
        key=(permutation,exponent)
        assert key not in acts,'two normal forms define the same projective matrix'
        acts[key]=(s,i,j)
    assert len(acts)==2*d*d
    pairs=0
    for s,i,j in group:
        for t,k,l in group:
            su=s*t;iu=(i+s*k)%d;ju=(j+s*l)%d;central=(j*s*k)%d
            for r in range(d):
                h=(k+t*r)%d
                assert (i+s*h)%d==(iu+su*r)%d
                assert (l*t*r+j*s*h)%d==(central+ju*su*r)%d
            pairs+=1
    return dict(schema='spur-exact-symmetry-v1',d=d,seed=20261102,
        q_equations=len(chart.q),homogeneous_terms=terms,
        invariance_generators=['X','Z','parity'],
        group_order=len(group),all_projective_normal_forms_distinct=True,
        multiplication_pairs_checked=pairs,
        multiplication='(s,i,j)*(t,k,l)=(s*t,i+s*k,j+s*l) modulo d, central phase zeta^(j*s*k)',
        action='U=X^i Z^j P^((1-s)/2); (a,b)->(Ua,U^(-T)b)',
        free_wedge='zeta^(j*r)*a[s*(r-i)]-a[r]*a[-s*i], for r=1,...,d-1',
        proof_scope='Exact homogeneous q invariance plus finite group law; root-level freeness still requires each interval witness.',
        status='PASS',seconds=round(time.monotonic()-start,6),python=sys.version,
        model_source_sha256=hashlib.sha256((H/'e10_face_system.py').read_bytes()).hexdigest())


def main():
    if not __debug__:raise RuntimeError('optimized Python disables certificate assertions')
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--d',type=int,choices=[6,7],required=True)
    args=ap.parse_args();result=verify(args.d)
    (H/f'e45_d{args.d}_symmetry.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
