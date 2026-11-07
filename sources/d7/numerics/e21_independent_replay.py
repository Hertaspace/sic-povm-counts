#!/usr/bin/env python3.14
"""Fresh full-support vertex coverage and independent ACFW modular replay.

No saved SMT is loaded. Verification uses ALL source exponents, without the
enumerator's componentwise-dominance reduction. Fixed seed 20261102.
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
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import sys
import time

sys.dont_write_bytecode = True
import z3
from e10_face_system import SEED, build_chart, primitive_root


def basis_of(rows):
    basis = []
    for rr in rows:
        row = list(map(F, rr))
        for pivot, bb in basis:
            a = row[pivot]
            row = [x-a*y for x,y in zip(row,bb)]
        pivot = next((j for j,x in enumerate(row) if x), None)
        if pivot is not None:
            a = row[pivot]
            basis.append((pivot, [x/a for x in row]))
    return basis


def belongs(row, basis):
    row = list(map(F,row))
    for pivot, bb in basis:
        a = row[pivot]
        row = [x-a*y for x,y in zip(row,bb)]
    return not any(row)


def direct_acfw(d,c,s,p):
    """Use the two signed integer labels and tau, not the product formula."""
    g = primitive_root(p)
    z = pow(g,(p-1)//(2*d),p)
    tau, omega = (-z)%p, z*z%p
    keep = [j for j in range(d) if j!=c]+[d+j for j in range(d) if j!=s]
    def zpoly(i,j):
        out = {}
        for k in range(d):
            ee = [0]*(2*d)
            ee[k] += 1
            ee[d+(k+i)%d] += 1
            out[tuple(ee)] = pow(tau,(i*j)%(2*d),p)*pow(omega,(j*k)%d,p)%p
        return out
    def multiply(aa,bb):
        out = {}
        for ea,ca in aa.items():
            for eb,cb in bb.items():
                ee = tuple(x+y for x,y in zip(ea,eb))
                out[ee] = (out.get(ee,0)+ca*cb)%p
        return out
    zz = multiply(zpoly(0,0),zpoly(0,0))
    out,seen = [],set()
    for i in range(d):
        for j in range(d):
            if (i,j)==(0,0) or (i,j) in seen:
                continue
            seen.update(((i,j),(-i%d,-j%d)))
            pp = multiply(zpoly(i,j),zpoly(-i,-j))
            keys = set(pp)|set(zz)
            local = {}
            for ee in keys:
                e = tuple(ee[k] for k in keep)
                cc = ((d+1)*pp.get(ee,0)-zz.get(ee,0))%p
                local[e] = (local.get(e,0)+cc)%p
            out.append({e:cc for e,cc in local.items() if cc})
    return tuple(out),omega


def replay(path, timeout=120):
    start=time.monotonic()
    saved=json.loads(path.read_text())
    d,c,s=saved['d'],saved['c'],saved['s']
    chart=build_chart(d,c,s)
    assert saved['complete'] is True and saved['termination']=='unsat'
    assert list(chart.names)==saved['names']
    digest=hashlib.sha256(json.dumps([chart.names,chart.support],separators=(',',':')).encode()).hexdigest()
    assert saved['support_sha256']==digest
    modular=[]
    for p in (30241,31081):
        original,omega=direct_acfw(d,c,s,p)
        reduced=build_chart(d,c,s,p)
        assert original==reduced.q and omega==reduced.omega
        for aa,bb in zip(chart.q,original):
            evaluated={e:sum(cc*pow(omega,j,p) for j,cc in enumerate(vv))%p for e,vv in aa.items()}
            evaluated={e:cc for e,cc in evaluated.items() if cc}
            assert evaluated==bb
        modular.append(dict(p=p,original_signed_acfw_product='PASS',cyclotomic_evaluation='PASS'))
    zero={chart.names.index(nm) for nm in saved['zero_names']}
    free=[j for j in range(chart.n) if j not in zero]
    k=len(free)
    exps=sorted({tuple(e[j] for j in free) for e in chart.support})
    w=[z3.Real('replay_w'+str(j)) for j in free]
    linear=[z3.Sum([a*x for a,x in zip(e,w) if a]) for e in exps]
    active=[l==1 for l in linear]
    solver=z3.Solver()
    solver.set(random_seed=SEED,timeout=timeout*1000)
    solver.add(*[x>0 for x in w],*[l>=1 for l in linear])
    solver.add(z3.PbGe([(aa,1) for aa in active],k))
    weights=[]
    for record in saved['weights']:
        ww=list(map(F,record['weight']))
        assert all(ww[j]==0 for j in zero)
        assert all(ww[j]>0 for j in free)
        assert all(sum(x*y for x,y in zip(e,ww))>=1 for e in chart.support)
        normals=[e for e in exps if sum(x*ww[j] for x,j in zip(e,free))==1]
        assert len(basis_of(normals))==k
        solver.add(z3.Or([x!=z3.RealVal(str(ww[j])) for x,j in zip(w,free)]))
        weights.append(record['weight'])
    cuts=0
    while True:
        answer=solver.check()
        if answer!=z3.sat:
            break
        model=solver.model()
        vv=[]
        for x in w:
            value=model.eval(x,model_completion=True)
            vv.append(F(value.numerator_as_long(),value.denominator_as_long()))
        normals=[e for e in exps if sum(x*y for x,y in zip(e,vv))==1]
        basis=basis_of(normals)
        if len(basis)==k:
            raise AssertionError('UNLISTED VERTEX '+str(vv))
        outside=[aa for e,aa in zip(exps,active) if not belongs(e,basis)]
        solver.add(z3.Or(outside))
        cuts+=1
    assert answer==z3.unsat, str(answer)+': '+solver.reason_unknown()
    return dict(file=path.name,d=d,c=c,s=s,zero_names=saved['zero_names'],
                complete_vertex_count=len(weights),weight=weights,
                full_support_projected_exponents=len(exps),rank_cuts=cuts,
                fresh_full_support_coverage=str(answer),modular=modular,
                seconds=round(time.monotonic()-start,6),status='PASS')


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('inputs',type=Path,nargs='+')
    ap.add_argument('--timeout',type=int,default=120)
    args=ap.parse_args()
    print(json.dumps(dict(seed=SEED,python=sys.version,z3=z3.get_version_string(),
                         verification='fresh full support, exact rational arithmetic, direct signed ACFW products')),flush=True)
    for path in args.inputs:
        print(json.dumps(replay(path,args.timeout)),flush=True)


if __name__=='__main__':
    main()
