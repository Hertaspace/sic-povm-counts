#!/usr/bin/env python3
"""Exact two-projector-orbit lower bound 2000+2000 for d=5 complex equations.

Standard library only.  Integer arithmetic in a proven degree-32 field;
the second projector is sigma(M), not |sigma(psi)><sigma(psi)|.
No claim of completeness without an independent 4000-root upper bound.
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

import ast
from collections import Counter, deque
from dataclasses import dataclass
import hashlib
from itertools import product
import json
from math import gcd, lcm
from pathlib import Path
import platform
import sys
import time

EXP=Path(__file__).resolve().parents[1]
ZERO=(0,)*32


def basis(a=0,b=0,c=0,h=0,e=0):
    z=[0]*32
    z[a+2*b+4*c+8*h+16*e]=1
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
    # u=sqrt3, t=sqrt5, R=2*r1, W=4*r2, i; all basis powers are 0 or 1.
    a=(u&1)+(v&1)
    b=((u>>1)&1)+((v>>1)&1)
    c=((u>>2)&1)+((v>>2)&1)
    h=((u>>3)&1)+((v>>3)&1)
    e=((u>>4)&1)+((v>>4)&1)
    if h==2:
        # W²=(-u+t+3)R+2ut+10u+t-5.
        terms=[(a+1,b,c+1,0,e,-1),(a,b+1,c+1,0,e,1),(a,b,c+1,0,e,3),
               (a+1,b+1,c,0,e,2),(a+1,b,c,0,e,10),(a,b+1,c,0,e,1),(a,b,c,0,e,-5)]
    else:
        terms=[(a,b,c,h,e,1)]
    out=[0]*32
    for a,b,c,h,e,coefficient in terms:
        # R²=10+2t.  c never exceeds 3 in a product of two basis monomials.
        rterms=[(b,c,coefficient)] if c<2 else [(b,c-2,10*coefficient),(b+1,c-2,2*coefficient)]
        for b,c,coefficient in rterms:
            coefficient*=3**(a//2)*5**(b//2)*(-1 if e==2 else 1)
            out[(a%2)+2*(b%2)+4*c+8*h+16*(e%2)]+=coefficient
    return tuple((j,x) for j,x in enumerate(out) if x)


TABLE=[[basis_product(u,v) for v in range(32)] for u in range(32)]


def mul(x,y):
    out=[0]*32
    ys=[(j,b) for j,b in enumerate(y) if b]
    for u,a in enumerate(x):
        if a:
            for v,b in ys:
                for w,c in TABLE[u][v]:
                    out[w]+=a*b*c
    return tuple(out)


def conjugate(x):
    return tuple(a if j<16 else -a for j,a in enumerate(x))


ONE=basis()
U=basis(a=1)
T=basis(b=1)
R=basis(c=1)
W=basis(h=1)
I=basis(e=1)


def primitive(v):
    factor=0
    for x in v:
        for a in x:
            factor=gcd(factor,abs(a))
    assert factor
    return tuple(tuple(a//factor for a in x) for x in v)


@dataclass
class Rational:
    num: tuple
    den: int=1

    def __post_init__(self):
        g=abs(self.den)
        for a in self.num:
            g=gcd(g,abs(a))
        if self.den<0:
            g=-g
        self.num=tuple(a//g for a in self.num)
        self.den//=g

    def __add__(self,other):
        return Rational(add(scalar(self.num,other.den),scalar(other.num,self.den)),self.den*other.den)

    def __sub__(self,other):
        return Rational(sub(scalar(self.num,other.den),scalar(other.num,self.den)),self.den*other.den)

    def __mul__(self,other):
        return Rational(mul(self.num,other.num),self.den*other.den)

    def __neg__(self):
        return Rational(neg(self.num),self.den)

    def __truediv__(self,other):
        assert all(a==0 for a in other.num[1:]) and other.num[0]
        return Rational(scalar(self.num,other.den),self.den*other.num[0])


def eval_exact(node,env):
    if isinstance(node,ast.Expression):
        return eval_exact(node.body,env)
    if isinstance(node,ast.Constant):
        assert isinstance(node.value,int)
        return Rational(scalar(ONE,node.value))
    if isinstance(node,ast.Name):
        return env[node.id]
    if isinstance(node,ast.List):
        return [eval_exact(x,env) for x in node.elts]
    if isinstance(node,ast.UnaryOp):
        value=eval_exact(node.operand,env)
        return -value if isinstance(node.op,ast.USub) else value
    if isinstance(node,ast.BinOp):
        a,b=eval_exact(node.left,env),eval_exact(node.right,env)
        if isinstance(node.op,ast.Add):
            return a+b
        if isinstance(node.op,ast.Sub):
            return a-b
        if isinstance(node.op,ast.Mult):
            return a*b
        if isinstance(node.op,ast.Div):
            return a/b
    raise ValueError(ast.dump(node))


def representative():
    source=(EXP/"calibration/sg_appendix_b_d4_d7.txt").read_text()
    chunk=source.split("\n5a\n",1)[1].split("\n6a\n",1)[0]
    expression=chunk.split("phi:=[",1)[1].split("];",1)[0]
    env={"w3":Rational(U),"w5":Rational(T),"w15":Rational(mul(U,T)),
         "r1":Rational(R,2),"r2":Rational(W,4),"I":Rational(I)}
    entries=eval_exact(ast.parse("["+expression+"]",mode="eval"),env)
    denominator=lcm(*(x.den for x in entries))
    return primitive(tuple(scalar(x.num,denominator//x.den) for x in entries))


def sigma_numerator(x):
    """Return 40*sigma(x); sigma fixes t,R,i and negates u."""
    out=ZERO
    for j,a in enumerate(x):
        if not a:
            continue
        sign=-1 if j&1 else 1
        if j&8:
            monomial=basis(j&1,(j>>1)&1,(j>>2)&1,0,(j>>4)&1)
            out=add(out,scalar(mul(monomial,SIGMA_W_NUM),a*sign))
        else:
            monomial=basis(j&1,(j>>1)&1,(j>>2)&1,0,(j>>4)&1)
            out=add(out,scalar(monomial,40*a*sign))
    return out


# sigma(A) replaces u by -u in A=W².  A*sigma(A)=-4*(R-t-5)².
A=mul(W,W)
A_SIGMA=tuple(-a if j&1 else a for j,a in enumerate(A))
C=sub(sub(R,T),scalar(ONE,5))
SIGMA_W_NUM=mul(mul(mul(mul(I,A_SIGMA),W),add(add(R,T),scalar(ONE,5))),
                sub(scalar(ONE,5),scalar(T,2)))


def roots_scaled():
    # rho[k]=8*zeta5^k, using zeta5=(t-1+iR)/4.
    z1=add(sub(scalar(T,2),scalar(ONE,2)),mul(I,scalar(R,2)))
    z2=add(neg(add(scalar(T,2),scalar(ONE,2))),mul(I,mul(sub(T,ONE),R)))
    return (scalar(ONE,8),z1,z2,conjugate(z2),conjugate(z1))


RHO=roots_scaled()


def apply_gate(letter,v,dual=False):
    sign=-1 if dual else 1
    if letter=="P":
        return primitive(tuple(mul(RHO[(sign*3*j*j)%5],v[j]) for j in range(5)))
    if letter=="S":
        out=[]
        for r in range(5):
            value=ZERO
            for s in range(5):
                value=add(value,mul(RHO[(sign*r*s)%5],v[s]))
            out.append(value)
        return primitive(tuple(out))
    raise ValueError(letter)


def apply_displacement(v,q,dual=False):
    a,b=q
    sign=-1 if dual else 1
    return tuple(mul(RHO[(sign*b*((j-a)%5))%5],v[(j-a)%5]) for j in range(5))


def identity_key():
    return (0,1,0,0,1,0,0)


def image_phase(A,x,y):
    _,a,b,c,e,r,s=A
    return (r*x+s*y+a*c*x*(x-1)+b*e*y*(y-1)+2*c*b*x*y)%10


def compose(A,B):
    ka,a,b,c,e,r,s=A
    kb,f,g,h,j,t,u=B
    sign=-1 if ka else 1
    return (ka^kb,(a*f+b*h)%5,(a*g+b*j)%5,(c*f+e*h)%5,(c*g+e*j)%5,
            (sign*t+image_phase(A,f,h))%10,(sign*u+image_phase(A,g,j))%10)


def mm(A,B):
    a,b,c,e=A
    f,g,h,j=B
    return ((a*f+b*h)%5,(a*g+b*j)%5,(c*f+e*h)%5,(c*g+e*j)%5)


def full_group():
    gens={"S":((0,4,1,0),(0,0,4,1,0,0,0)),
          "P":((1,0,1,1),(0,1,0,1,1,6,0))}
    identity=(1,0,0,1)
    sl={identity:{"key":identity_key(),"word":"","parent":None,"last":None}}
    queue=deque([identity])
    while queue:
        F=queue.popleft()
        for name,(G,key) in gens.items():
            H=mm(G,F)
            if H not in sl:
                sl[H]={"key":compose(key,sl[F]["key"]),"word":sl[F]["word"]+name,
                       "parent":F,"last":name}
                queue.append(H)
    assert set(sl)=={f for f in product(range(5),repeat=4) if (f[0]*f[3]-f[1]*f[2])%5==1}
    assert len(sl)==120
    K=(1,1,0,0,4,0,0)
    group={}
    for anti in (0,1):
        for F,R0 in sl.items():
            basekey=compose(R0["key"],K) if anti else R0["key"]
            for a,b in product(range(5),repeat=2):
                dq=(0,1,0,0,1,(2*b)%10,(-2*a)%10)
                key=compose(dq,basekey)
                assert key not in group
                group[key]={"F_lift":[list(F[:2]),list(F[2:])],"word":R0["word"],"q":[a,b],"anti":bool(anti)}
    expected={(anti,a,b,c,e,r,s) for anti in (0,1) for a,b,c,e in product(range(5),repeat=4)
              if (a*e-b*c-(-1 if anti else 1))%5==0 for r,s in product(range(0,10,2),repeat=2)}
    assert set(group)==expected and len(group)==6000
    return group,sl


def ray_fixed(v,w):
    assert v[0]!=ZERO
    return all(mul(w[j],v[0])==mul(w[0],v[j]) for j in range(1,5))


def pair_norm(a,b):
    value=ZERO
    for x,y in zip(a,b):
        value=add(value,mul(x,y))
    return value


def verify_quartics(a,b):
    N=pair_norm(a,b)
    assert N!=ZERO
    N2=mul(N,N)
    for k,ell in product(range(5),repeat=2):
        value=ZERO
        for j in range(5):
            value=add(value,mul(mul(a[j],b[(j+k)%5]),mul(b[(j+ell)%5],a[(j+k+ell)%5])))
        assert sub(scalar(value,6),scalar(N2,int(k==0)+int(ell==0)))==ZERO,(k,ell)
    return N


def verify_trace_products(a,b,N):
    """Independent exact 24 displacement-product checks; omitted scales are 8."""
    N2=mul(N,N)
    checked=0
    for p,q in product(range(5),repeat=2):
        if (p,q)==(0,0):
            continue
        forward=apply_displacement(a,(p,q))
        inverse=tuple(mul(RHO[(-q*j)%5],a[(j+p)%5]) for j in range(5))
        lhs=mul(pair_norm(forward,b),pair_norm(inverse,b))
        assert sub(scalar(lhs,6),scalar(N2,64))==ZERO,(p,q)
        checked+=1
    assert checked==24


def hermitian_witness(a,b,N):
    for j,k in product(range(5),repeat=2):
        residual=sub(mul(mul(a[j],b[k]),conjugate(N)),
                     mul(conjugate(mul(a[k],b[j])),N))
        if residual!=ZERO:
            return {"indices":[j,k],"nonzero_residual_basis":list(residual)}
    return None


def exact_order(key):
    x=identity_key()
    for n in range(1,101):
        x=compose(key,x)
        if x==identity_key():
            return n
    raise AssertionError(key)


def enumerate_pair_orbit(a,b,group,sl,label):
    stable=[]
    zero_right=zero_left=0
    attempted=0
    Z=compose((0,1,0,1,1,6,0),(0,0,4,1,0,0,0))
    for anti in (0,1):
        # The algebraic complexification of physical antiunitary action is
        # M -> U M^T U^dagger: it swaps the independent right/left vectors.
        # Actual entrywise conjugation agrees only on Hermitian projectors.
        source=(b,a) if anti else (a,b)
        images={}
        for F,R0 in sl.items():
            if R0["parent"] is None:
                images[F]=source
            else:
                old=images[R0["parent"]]
                images[F]=(apply_gate(R0["last"],old[0]),apply_gate(R0["last"],old[1],dual=True))
        for key,entry in group.items():
            if int(entry["anti"])!=anti:
                continue
            F=tuple(entry["F_lift"][0]+entry["F_lift"][1])
            x,y=images[F]
            wa=apply_displacement(x,entry["q"])
            wb=apply_displacement(y,entry["q"],dual=True)
            attempted+=1
            zero_right+=int(wa[0]==ZERO)
            zero_left+=int(wb[0]==ZERO)
            if ray_fixed(a,wa) and ray_fixed(b,wb):
                E=dict(entry)
                E["exact_key"]=list(key)
                E["projective_order"]=exact_order(key)
                if E["projective_order"]==3:
                    for q,Q in group.items():
                        if compose(key,q)==compose(q,Z):
                            E["Zauner_projective_conjugator"]=dict(Q)
                            E["Zauner_projective_conjugator"]["exact_key"]=list(q)
                            break
                    assert "Zauner_projective_conjugator" in E
                stable.append(E)
    assert attempted==6000 and not zero_right and not zero_left
    assert len(stable)==3 and Counter(E["projective_order"] for E in stable)=={1:1,3:2}
    assert all(not E["anti"] for E in stable)
    print("ORBIT",label,"EC",attempted,"stabilizer",len(stable),"chart rays",attempted//len(stable),flush=True)
    return {"enumerated_projective_elements":attempted,"stabilizer_order":len(stable),"stabilizer":stable,
            "zero_right_first_coordinates":zero_right,"zero_left_first_coordinates":zero_left,
            "projector_orbit_size":attempted//len(stable),"chart_root_count":attempted//len(stable)}


def check_field_and_sigma():
    assert mul(U,U)==scalar(ONE,3)
    assert mul(T,T)==scalar(ONE,5)
    assert mul(R,R)==add(scalar(ONE,10),scalar(T,2))
    assert mul(I,I)==neg(ONE)
    assert mul(A,A_SIGMA)==neg(scalar(mul(C,C),4))
    assert mul(SIGMA_W_NUM,SIGMA_W_NUM)==scalar(A_SIGMA,1600)
    assert SIGMA_W_NUM!=ZERO and conjugate(SIGMA_W_NUM)==neg(SIGMA_W_NUM)
    # Generator relations plus involution make sigma an automorphism of K.
    assert sigma_numerator(U)==neg(scalar(U,40))
    assert sigma_numerator(T)==scalar(T,40)
    assert sigma_numerator(R)==scalar(R,40)
    assert sigma_numerator(I)==scalar(I,40)
    assert sigma_numerator(W)==SIGMA_W_NUM
    elements=[basis(j&1,(j>>1)&1,(j>>2)&1,(j>>3)&1,(j>>4)&1) for j in range(32)]
    for x in elements:
        assert sigma_numerator(sigma_numerator(x))==scalar(x,1600)
    # Exhaustive associativity on basis triples certifies the multiplication table.
    for x,y,z in product(elements,repeat=3):
        assert mul(mul(x,y),z)==mul(x,mul(y,z))
    for x,y in product(elements,repeat=2):
        assert mul(x,y)==mul(y,x)
        assert conjugate(mul(x,y))==mul(conjugate(x),conjugate(y))
        assert scalar(sigma_numerator(mul(x,y)),40)==mul(sigma_numerator(x),sigma_numerator(y))
    # The base field is Q(zeta60), and reduction zeta60 -> 2 mod 61
    # makes A a nonsquare, so adjoining W doubles degree 16 to degree 32.
    p,z=61,2
    assert all(pow(z,60//q,p)!=1 for q in (2,3,5)) and pow(z,60,p)==1
    up=(pow(z,5,p)+pow(z,55,p))%p
    tp=(1+2*(pow(z,12,p)+pow(z,48,p)))%p
    rp=(2*(pow(z,3,p)+pow(z,57,p)))%p
    ip=pow(z,15,p)
    Ap=((-up+tp+3)*rp+2*up*tp+10*up+tp-5)%p
    assert (up,tp,rp,ip,Ap)==(53,26,1,11,50)
    assert pow(Ap,30,p)==60
    assert all(mul(RHO[1],RHO[j])==scalar(RHO[(j+1)%5],8) for j in range(5))
    assert add(add(add(add(RHO[0],RHO[1]),RHO[2]),RHO[3]),RHO[4])==ZERO
    assert all(sigma_numerator(x)==scalar(x,40) for x in RHO)
    return {"base_field":"Q(zeta60)","base_degree":16,"field_degree":32,
            "nonsquare_prime":61,"zeta60_residue":2,"u_t_R_i_A_residues":[up,tp,rp,ip,Ap],
            "A_legendre_residue":pow(Ap,30,p),"sigma_W_numerator_basis":list(SIGMA_W_NUM),
            "sigma_W_denominator":40,"sigma_order":2,"sigma_base_cyclotomic_exponent":41,
            "sigma_fixes_zeta5":True,"sigma_commutes_with_complex_conjugation":False}


def main():
    started=time.perf_counter()
    field=check_field_and_sigma()
    print("FIELD PASS: degree 32; explicit order-2 sigma does not commute with conjugation",flush=True)
    v=representative()
    b=tuple(conjugate(x) for x in v)
    N=verify_quartics(v,b)
    verify_trace_products(v,b,N)
    assert hermitian_witness(v,b,N) is None
    sa=primitive(tuple(sigma_numerator(x) for x in v))
    sb=primitive(tuple(sigma_numerator(x) for x in b))
    SN=verify_quartics(sa,sb)
    verify_trace_products(sa,sb,SN)
    witness=hermitian_witness(sa,sb,SN)
    assert witness is not None
    print("PROJECTORS PASS: true Hermitian and sigma-image non-Hermitian; 25 quartics + 24 trace products each",flush=True)
    group,sl=full_group()
    print("GROUP PASS: 6000 exact projective EC elements",flush=True)
    actual=enumerate_pair_orbit(v,b,group,sl,"Hermitian SG5a")
    conjugate_orbit=enumerate_pair_orbit(sa,sb,group,sl,"non-Hermitian sigma(M)")
    if (EXP/"calibration/e03_clifford_calibration.json").exists():
        numeric=json.loads((EXP/"calibration/e03_clifford_calibration.json").read_text())
        assert {tuple(E["exact_key"]) for E in actual["stabilizer"]}=={
            tuple(E["exact_key"]) for E in numeric["orbits"]["5a"]["stabilizer"]}
    result={"python":sys.version,"platform":platform.platform(),"seed":20261022,
            "arithmetic":"exact 32-dimensional integer basis u^a t^b R^c W^h i^e",
            "source":"Scott--Grassl arXiv:0910.5784 Appendix B p.167",
            "field":field,"representative_right_basis":v,"representative_left_basis":b,
            "sigma_projector_right_basis":sa,"sigma_projector_left_basis":sb,
            "original_pair_norm_basis":list(N),"sigma_pair_norm_basis":list(SN),
            "nonHermitian_projector_witness":witness,
            "original_exact_quartic_count":25,"sigma_exact_quartic_count":25,
            "original_exact_WH_trace_product_count":24,"sigma_exact_WH_trace_product_count":24,
            "group_order":len(group),"orbits":{"Hermitian_SG5a":actual,"nonHermitian_sigmaM":conjugate_orbit},
            "disjointness":"Hermitian vs non-Hermitian, preserved by unitary conjugation and the complexified anti action M -> U M^T U^dagger",
            "complexified_anti_action":"transpose M, equivalently swap the independent right/left vectors",
            "distinct_complex_chart_projectors_lower_bound":actual["chart_root_count"]+conjugate_orbit["chart_root_count"],
            "distinct_physical_chart_SIC_rays_lower_bound":actual["chart_root_count"],
            "scope":"lower bounds only; complete classification requires an independent exact quotient dimension upper bound 4000",
            "group_keys_sha256":hashlib.sha256(json.dumps(sorted(group)).encode()).hexdigest(),
            "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "source_sha256":hashlib.sha256((EXP/"calibration/sg_appendix_b_d4_d7.txt").read_bytes()).hexdigest(),
            "elapsed_seconds":time.perf_counter()-started}
    output=EXP/"certificates/e09_exact_d5.json"
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(result,indent=2)+"\n")
    print("PASS: 2000 exact Hermitian roots + 2000 disjoint exact non-Hermitian roots",flush=True)
    print("SECONDS",result["elapsed_seconds"],flush=True)


if __name__=="__main__":
    main()
