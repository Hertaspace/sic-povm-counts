#!/usr/bin/env python3
"""Exact SG4a SIC, full projective EC stabilizer, and 256-ray chart orbit.

Standard library only; integer arithmetic in Q(s,t,r,i),
s²=2, t²=5, r²=1+t, i²=-1.  No floating-point membership decisions.
Source: Scott--Grassl arXiv:0910.5784 Appendix B, p.167.
This proves a known orbit lower bound; it does not alone classify all SICs.
"""
from __future__ import annotations

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

from collections import Counter, deque
import hashlib
from itertools import product
import json
from math import gcd
from pathlib import Path
import platform
import sys
import time

EXP=Path(__file__).resolve().parents[1]
ZERO=(0,)*16


def basis(a=0,b=0,c=0,e=0):
    z=[0]*16
    z[a+2*b+4*c+8*e]=1
    return tuple(z)


def add(x,y):
    return tuple(a+b for a,b in zip(x,y))


def neg(x):
    return tuple(-a for a in x)


def sub(x,y):
    return tuple(a-b for a,b in zip(x,y))


def scalar(x,n):
    return tuple(a*n for a in x)


def basis_product(u,v):
    a=(u&1)+(v&1)
    b=((u>>1)&1)+((v>>1)&1)
    c=((u>>2)&1)+((v>>2)&1)
    e=((u>>3)&1)+((v>>3)&1)
    terms=[(a,b,c,e)] if c<2 else [(a,b,0,e),(a,b+1,0,e)]
    out=[0]*16
    for a,b,c,e in terms:
        coefficient=2**(a//2)*5**(b//2)*(-1 if e==2 else 1)
        out[(a%2)+2*(b%2)+4*c+8*(e%2)]+=coefficient
    return tuple((j,x) for j,x in enumerate(out) if x)


TABLE=[[basis_product(u,v) for v in range(16)] for u in range(16)]


def mul(x,y):
    out=[0]*16
    for u,a in enumerate(x):
        if a:
            for v,b in enumerate(y):
                if b:
                    for w,c in TABLE[u][v]:
                        out[w]+=a*b*c
    return tuple(out)


def conjugate(x):
    return tuple(a if j<8 else -a for j,a in enumerate(x))


ONE=basis()
SQRT2=basis(a=1)
SQRT5=basis(b=1)
RADICAL=basis(c=1)
I=basis(e=1)


def phase_i(x,n):
    n%=4
    if n==0:
        return x
    if n==2:
        return neg(x)
    times_i=tuple(-a for a in x[8:])+x[:8]
    return times_i if n==1 else neg(times_i)


def primitive(v):
    factor=0
    for x in v:
        for a in x:
            factor=gcd(factor,abs(a))
    assert factor>0
    return tuple(tuple(a//factor for a in x) for x in v)


def representative():
    s,t,r=SQRT2,SQRT5,RADICAL
    st=mul(s,t)
    common_real=mul(add(st,s),r)
    common_imag=mul(sub(add(st,s),add(scalar(t,2),scalar(ONE,2))),r)
    v1=add(add(common_real,sub(scalar(s,4),scalar(ONE,4))),
           phase_i(sub(common_imag,scalar(ONE,4)),1))
    v2=phase_i(sub(scalar(s,8),scalar(ONE,8)),1)
    v3=add(sub(common_real,sub(scalar(s,4),scalar(ONE,4))),
           phase_i(add(common_imag,scalar(ONE,4)),1))
    return (scalar(ONE,8),v1,v2,v3)


def apply_gate(letter,v):
    if letter=="S":
        # Projectively S is the DFT with entries i^(row*column), omitting 1/2.
        return primitive(tuple(tuple(sum(phase_i(v[s],r*s)[j] for s in range(4))
                                     for j in range(16)) for r in range(4)))
    if letter=="P":
        # sqrt(2) times diag(tau^(j²)); one common nonzero scale is omitted.
        minus_one_i=neg(add(ONE,I))
        diagonal=(SQRT2,minus_one_i,neg(SQRT2),minus_one_i)
        return primitive(tuple(mul(a,b) for a,b in zip(diagonal,v)))
    raise ValueError(letter)


def apply_displacement(v,q):
    a,b=q
    return tuple(phase_i(v[(j-a)%4],b*((j-a)%4)) for j in range(4))


def identity_key():
    return (0,1,0,0,1,0,0)


def image_phase(A,x,y):
    _,a,b,c,e,r,s=A
    return (r*x+s*y+a*c*x*(x-1)+b*e*y*(y-1)+2*c*b*x*y)%8


def compose(A,B):
    ka,a,b,c,e,r,s=A
    kb,f,g,h,j,t,u=B
    sign=-1 if ka else 1
    return (ka^kb,(a*f+b*h)%4,(a*g+b*j)%4,(c*f+e*h)%4,(c*g+e*j)%4,
            (sign*t+image_phase(A,f,h))%8,(sign*u+image_phase(A,g,j))%8)


def matrix_mul(A,B):
    a,b,c,e=A
    f,g,h,j=B
    return ((a*f+b*h)%8,(a*g+b*j)%8,(c*f+e*h)%8,(c*g+e*j)%8)


def displacement_key(q):
    a,b=q
    return (0,1,0,0,1,(2*b)%8,(-2*a)%8)


def order(key):
    x=identity_key()
    for n in range(1,101):
        x=compose(key,x)
        if x==identity_key():
            return n
    raise AssertionError(key)


def exact_group_images(v):
    G={"S":((0,7,1,0),(0,0,3,1,0,0,0)),
       "P":((1,0,1,1),(0,1,0,1,1,5,0))}
    Iden=(1,0,0,1)
    sl={Iden:{"key":identity_key(),"word":"","images":(v,tuple(conjugate(x) for x in v))}}
    queue=deque([Iden])
    while queue:
        f=queue.popleft()
        R=sl[f]
        for name,(matrix,key) in G.items():
            h=matrix_mul(matrix,f)
            if h not in sl:
                sl[h]={"key":compose(key,R["key"]),"word":R["word"]+name,
                       "images":tuple(apply_gate(name,x) for x in R["images"])}
                queue.append(h)
    exact_sl={f for f in product(range(8),repeat=4) if (f[0]*f[3]-f[1]*f[2])%8==1}
    assert set(sl)==exact_sl and len(sl)==384
    K=(1,1,0,0,3,0,0)
    group={}
    raw=0
    multiplicity=Counter()
    for anti in (0,1):
        for f,R in sl.items():
            source=R["images"][anti]
            basekey=compose(R["key"],K) if anti else R["key"]
            for q in product(range(4),repeat=2):
                raw+=1
                key=compose(displacement_key(q),basekey)
                multiplicity[key]+=1
                if key not in group:
                    group[key]={"F_lift":[list(f[:2]),list(f[2:])],"word":R["word"],
                                "q":list(q),"anti":bool(anti),"image":apply_displacement(source,q)}
    assert raw==12288 and set(multiplicity.values())=={8}
    expected=set()
    for anti in (0,1):
        for a,b,c,e in product(range(4),repeat=4):
            if (a*e-b*c-(-1 if anti else 1))%4==0:
                for r in range((a*c)%2,8,2):
                    for s in range((b*e)%2,8,2):
                        expected.add((anti,a,b,c,e,r,s))
    assert set(group)==expected and len(group)==1536
    return group


def fixes_ray(v,w):
    assert v[0]!=ZERO
    return all(mul(w[j],v[0])==mul(w[0],v[j]) for j in range(1,4))


def verify_sic(v):
    n=ZERO
    for z in v:
        n=add(n,mul(z,conjugate(z)))
    n2=mul(n,n)
    quartics=[]
    for k,ell in product(range(4),repeat=2):
        value=ZERO
        for j in range(4):
            term=mul(mul(v[j],conjugate(v[(j+k)%4])),
                     mul(conjugate(v[(j+ell)%4]),v[(j+k+ell)%4]))
            value=add(value,term)
        assert sub(scalar(value,5),scalar(n2,int(k==0)+int(ell==0)))==ZERO
        quartics.append([k,ell])
    overlaps=[]
    for q in product(range(4),repeat=2):
        if q==(0,0):
            continue
        w=apply_displacement(v,q)
        o=ZERO
        for x,y in zip(v,w):
            o=add(o,mul(conjugate(x),y))
        assert sub(scalar(mul(o,conjugate(o)),5),n2)==ZERO
        overlaps.append(list(q))
    return {"norm_squared_basis":list(n),"quartic_zero_residuals":quartics,
            "WH_overlap_zero_residuals":overlaps}


def check_ring():
    assert mul(SQRT2,SQRT2)==scalar(ONE,2)
    assert mul(SQRT5,SQRT5)==scalar(ONE,5)
    assert mul(RADICAL,RADICAL)==add(ONE,SQRT5)
    assert mul(I,I)==neg(ONE)
    elements=[basis(j&1,(j>>1)&1,(j>>2)&1,(j>>3)&1) for j in range(16)]
    for a,b,c in product(elements,repeat=3):
        assert mul(mul(a,b),c)==mul(a,mul(b,c))
    for a,b in product(elements,repeat=2):
        assert conjugate(mul(a,b))==mul(conjugate(a),conjugate(b))
        assert mul(a,b)==mul(b,a)


def main():
    started=time.perf_counter()
    check_ring()
    v=representative()
    result=verify_sic(v)
    print("SIC PASS: 16 Fourier quartics and 15 nonidentity WH overlaps",flush=True)
    group=exact_group_images(v)
    stable=[]
    zeros=[]
    Z=compose((0,1,0,1,1,5,0),(0,0,3,1,0,0,0))
    for key,R in group.items():
        if R["image"][0]==ZERO:
            zeros.append(list(key))
        if fixes_ray(v,R["image"]):
            entry={k:value for k,value in R.items() if k!="image"}
            entry["exact_key"]=list(key)
            entry["projective_order"]=order(key)
            if entry["projective_order"]==3:
                for q,Q in group.items():
                    if compose(key,q)==compose(q,Z):
                        entry["Zauner_projective_conjugator"]={k:value for k,value in Q.items() if k!="image"}
                        entry["Zauner_projective_conjugator"]["exact_key"]=list(q)
                        break
                assert "Zauner_projective_conjugator" in entry
            stable.append(entry)
    assert len(stable)==6 and not zeros
    assert sum(not E["anti"] for E in stable)==3
    assert Counter(E["projective_order"] for E in stable)=={1:1,2:1,3:2,6:2}
    if (EXP/"calibration/e03_clifford_calibration.json").exists():
        numeric=json.loads((EXP/"calibration/e03_clifford_calibration.json").read_text())
        assert {tuple(E["exact_key"]) for E in stable}=={
            tuple(E["exact_key"]) for E in numeric["orbits"]["4a"]["stabilizer"]}
    result.update({"python":sys.version,"platform":platform.platform(),"seed":20261022,
                   "source":"Scott--Grassl arXiv:0910.5784 Appendix B p.167",
                   "arithmetic":"16-dimensional exact integer basis s^a t^b r^c i^e, s^2=2,t^2=5,r^2=1+t,i^2=-1",
                   "field_degree_over_Q":16,"representative_basis":v,
                   "SL_lift_order":384,"raw_representations":12288,"kernel_multiplicity":8,
                   "projective_EC_order":len(group),"all_admissible_XZ_actions_checked":True,
                   "stabilizer_order":len(stable),"stabilizer":stable,
                   "zero_first_coordinate_images":len(zeros),"projective_orbit_rays":len(group)//len(stable),
                   "chart_psi0_nonzero_rays":len(group)//len(stable),
                   "scope":"exact lower bound 256 known-orbit SIC rays in the chart; classification of all roots requires an independent upper bound",
                   "group_keys_sha256":hashlib.sha256(json.dumps(sorted(group)).encode()).hexdigest(),
                   "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                   "elapsed_seconds":time.perf_counter()-started})
    output=EXP/"certificates/e07_exact_d4.json"
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(result,indent=2)+"\n")
    print("GROUP PASS: all 1536 exact projective EC elements, stabilizer=6, unitary=3, antiunitary=3",flush=True)
    print("CHART PASS: zero first coordinates=0, distinct exact known SIC rays=256",flush=True)
    print("ZAUNER PASS: both order-3 stabilizers exactly projectively conjugate to Fz",flush=True)
    print("SECONDS",result["elapsed_seconds"],flush=True)


if __name__=="__main__":
    main()
