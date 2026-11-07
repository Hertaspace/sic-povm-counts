#!/usr/bin/env python3
"""Exact whole-fibre reconstruction, per-point tangent data, and permutations.

The input chart is certified complete by its number of points equalling vdim.
WH translates of a0*b0!=0 cover Y, proved from Z(0,1)!=0.
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
import json,sys,time,platform
from collections import Counter,deque
from e02_groups import GF,Model,matrix_rank

ROOT=Path(__file__).resolve().parents[1]
def wh(M,P,r,s):
    F=M.field; d=M.d; a,b=P
    return M.normalize_point((tuple(F.mul(a[(j-r)%d],F.pow(M.omega,s*(j-r))) for j in range(d)),
                              tuple(F.mul(b[(j-r)%d],F.pow(M.omega,-s*(j-r))) for j in range(d))))
def gate(M,P,g):
    F=M.field;d=M.d;a,b=P
    if g=='S':
        return M.normalize_point((tuple(F.mul(x,F.pow(M.tau,j*j)) for j,x in enumerate(a)),
                                  tuple(F.mul(x,F.pow(M.tau,-j*j)) for j,x in enumerate(b))))
    if g=='F':
        return M.normalize_point((tuple(F.sum(F.mul(a[j],F.pow(M.omega,i*j)) for j in range(d)) for i in range(d)),
                                  tuple(F.sum(F.mul(b[j],F.pow(M.omega,-i*j)) for j in range(d)) for i in range(d))))
    return wh(M,P,1 if g=='X' else 0,1 if g=='Z' else 0)
def cycles(perm):
    unseen=set(range(len(perm)));out=[]
    while unseen:
        first=min(unseen);cy=[];i=first
        while i in unseen:unseen.remove(i);cy.append(i);i=perm[i]
        assert i==first;out.append(cy)
    return out
def orbit_partition(points,actions):
    index={P:i for i,P in enumerate(points)};unseen=set(points);out=[]
    while unseen:
        start=min(unseen);seen={start};Q=deque([start])
        while Q:
            P=Q.popleft()
            for action in actions:
                P1=action(P)
                assert P1 in index,'group image outside complete fibre'
                if P1 not in seen:seen.add(P1);Q.append(P1)
        unseen-=seen;out.append(sorted(index[P] for P in seen))
    return out
def main():
    source=Path(sys.argv[1]);dat=json.loads(source.read_text());F=GF(dat['p'],dat['modulus']);d=dat['d']
    assert dat['complete_reduced_chart'],'need complete reduced chart to certify the whole fibre'
    M=Model(F,d,F.find_element_of_order(d if d%2 else 2*d));start=time.monotonic()
    chart=[M.normalize_point(P) for P in dat['points']]
    points=sorted({wh(M,P,r,0) for P in chart for r in range(d)})
    index={P:i for i,P in enumerate(points)}
    assert {P for P in points if P[0][0] and P[1][0]}==set(chart)
    perpoint=[]
    for i,P in enumerate(points):
        jac=M.jacobian_data(P,with_matrix=True);assert jac['on_nullfiber']
        rank,piv,rr=matrix_rank(F,jac['rows_equal'],jac['nvars'],return_rref=True)
        assert rank==jac['nvars']-1 and jac['rank_null']==jac['nvars']
        free=next(j for j in range(jac['nvars']) if j not in piv);tangent=[0]*jac['nvars'];tangent[free]=1
        for k,j in enumerate(piv):tangent[j]=F.neg(rr[k][free])
        dz=F.sum(F.mul(x,y) for x,y in zip(tangent,jac['row_trace']));assert dz
        tangent=[F.div(x,dz) for x in tangent]
        for key in ['rows_equal','row_trace','residuals']:jac.pop(key)
        perpoint.append({'id':i,'point':P,'jacobian':jac,'tangent_basis_dN_equal_1':tangent,
                         'local_length':2,'local_algebra':'k[N]/(N^2)','frobenius':M.frobenius_data(P)})
    whorbs=orbit_partition(points,[lambda P:wh(M,P,1,0),lambda P:wh(M,P,0,1)])
    corbs=orbit_partition(points,[lambda P:gate(M,P,g) for g in ()]) if False else orbit_partition(points,[lambda P,g=g:gate(M,P,g) for g in ['X','Z','S','F']])
    perm=[index[M.frobenius_point(P,1)] for P in points];cycs=cycles(perm)
    res={'d':d,'p':F.p,'q':F.q,'modulus':list(F.modulus),'tau':M.tau,'omega':M.omega,
         'seed':20261031,'python':platform.python_version(),'arithmetic':'exact finite field',
         'chart_points':len(chart),'whole_fibre_points':len(points),'whole_fibre_coverage':'WH shifts cover a_i*b_i!=0; these opens cover t!=0',
         'jacobian_counts':dict(Counter((x['jacobian']['rank_equal'],x['jacobian']['rank_null']) for x in perpoint)),
         'WH_orbits':whorbs,'Clifford_orbits':corbs,'Frob_p_permutation':perm,'Frob_p_cycles':cycs,'per_point':perpoint,
         'elapsed':time.monotonic()-start}
    res['jacobian_counts']={str(k):v for k,v in res['jacobian_counts'].items()}
    dest=ROOT/'numerics'/f'e05_d{d}_p{F.p}.json';dest.write_text(json.dumps(res,indent=2))
    print({k:v for k,v in res.items() if k not in ['per_point','WH_orbits','Clifford_orbits','Frob_p_permutation','Frob_p_cycles']})
    print('WH orbit sizes',dict(Counter(map(len,whorbs))))
    print('Clifford orbit sizes',dict(Counter(map(len,corbs))))
    print('absolute Frobenius cycle sizes',dict(Counter(map(len,cycs))))
    print('first point',perpoint[0])
if __name__=='__main__':main()
