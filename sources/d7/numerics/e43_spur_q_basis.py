#!/usr/bin/env python3.14
"""Exact Q(zeta_d) basis and portable row identities for the raw q-space.

Server only. No floating point or model-specific numerical solution is used.
The independent rank witness is a nonzero minor at a split prime. Spanning
identities are then checked coefficientwise in Q[z]/Phi_d.
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
from fractions import Fraction as Q
import hashlib
import json
from math import isqrt
from pathlib import Path
import sys
import time
sys.dont_write_bytecode=True
from e10_face_system import build_chart,root_vectors,primitive_root

H=Path(__file__).resolve().parent


def trim(a):
    a=list(a)
    while a and a[-1]==0:a.pop()
    return a


def padd(a,b,scale=Q(1)):
    out=list(a)+[Q(0)]*max(0,len(b)-len(a))
    for j,x in enumerate(b):out[j]+=scale*x
    return trim(out)


def pmul(a,b):
    if not a or not b:return []
    out=[Q(0)]*(len(a)+len(b)-1)
    for j,x in enumerate(a):
        if x:
            for k,y in enumerate(b):
                if y:out[j+k]+=x*y
    return trim(out)


def pdiv(a,b):
    a=trim(a);b=trim(b)
    if not b:raise ZeroDivisionError
    quo=[Q(0)]*max(0,len(a)-len(b)+1)
    while len(a)>=len(b):
        j=len(a)-len(b);v=a[-1]/b[-1];quo[j]=v
        for k,x in enumerate(b):a[j+k]-=v*x
        a=trim(a)
    return trim(quo),a


class Field:
    def __init__(self,phi):
        self.phi=tuple(map(Q,phi));self.k=len(phi)-1
        self.zero=(Q(0),)*self.k;self.one=(Q(1),)+(Q(0),)*(self.k-1)
    def element(self,x):
        if isinstance(x,(int,Q)):return (Q(x),)+(Q(0),)*(self.k-1)
        out=list(map(Q,x))
        if len(out)>self.k:out=pdiv(out,self.phi)[1]
        return tuple(out+[Q(0)]*(self.k-len(out)))
    def add(self,a,b):return tuple(x+y for x,y in zip(a,b))
    def sub(self,a,b):return tuple(x-y for x,y in zip(a,b))
    def mul(self,a,b):
        if a==self.zero or b==self.zero:return self.zero
        return self.element(pmul(a,b))
    def inv(self,a):
        if a==self.zero:raise ZeroDivisionError
        r0,r1=list(self.phi),trim(a);t0,t1=[],[Q(1)]
        while r1:
            quo,rem=pdiv(r0,r1)
            r0,r1=r1,rem;t0,t1=t1,padd(t0,pmul(quo,t1),Q(-1))
        assert len(r0)==1 and r0[0]
        out=self.element([x/r0[0] for x in t0])
        assert self.mul(a,out)==self.one
        return out


def modular_rows(rows,p):
    mat=[list(row) for row in rows];ids=list(range(len(mat)))
    piv=[];chosen=[];r=0
    for c in range(len(mat[0])):
        k=next((i for i in range(r,len(mat)) if mat[i][c]%p),None)
        if k is None:continue
        mat[r],mat[k]=mat[k],mat[r];ids[r],ids[k]=ids[k],ids[r]
        iv=pow(mat[r][c],-1,p);mat[r]=[x*iv%p for x in mat[r]]
        for i in range(r+1,len(mat)):
            if mat[i][c]:
                v=mat[i][c];mat[i]=[(x-v*y)%p for x,y in zip(mat[i],mat[r])]
        chosen.append(ids[r]);piv.append(c);r+=1
        if r==len(mat):break
    return chosen,piv


def det_mod(rows,p):
    mat=[row[:] for row in rows];out=1
    for j in range(len(mat)):
        k=next((i for i in range(j,len(mat)) if mat[i][j]%p),None)
        if k is None:return 0
        if k!=j:mat[j],mat[k]=mat[k],mat[j];out=-out
        v=mat[j][j];out=out*v%p;iv=pow(v,-1,p)
        for i in range(j+1,len(mat)):
            f=mat[i][j]*iv%p
            for c in range(j,len(mat)):mat[i][c]=(mat[i][c]-f*mat[j][c])%p
    return out%p


def generate(d,p=30241):
    start=time.monotonic();chart=build_chart(d,0,1)
    K=Field(chart.cyclotomic);mons=list(chart.support)
    matrix=[[K.element(f.get(e,K.zero)) for e in mons] for f in chart.q]
    assert (p-1)%(2*d)==0
    omega=pow(primitive_root(p),(p-1)//d,p)
    mod=lambda a:sum(int(x)*pow(omega,i,p) for i,x in enumerate(a))%p
    reduced=[[mod(a) for a in row] for row in matrix]
    chosen,piv=modular_rows(reduced,p);r=len(chosen)
    minor=det_mod([[reduced[j][c] for c in piv] for j in chosen],p)
    assert minor!=0
    R=[matrix[j][:] for j in chosen]
    T=[[K.one if i==j else K.zero for j in range(r)] for i in range(r)]
    piv_exact=[];k=0
    for c in range(len(mons)):
        row=next((i for i in range(k,r) if R[i][c]!=K.zero),None)
        if row is None:continue
        R[k],R[row]=R[row],R[k];T[k],T[row]=T[row],T[k]
        inv=K.inv(R[k][c]);R[k]=[K.mul(a,inv) for a in R[k]];T[k]=[K.mul(a,inv) for a in T[k]]
        for i in range(r):
            if i!=k and R[i][c]!=K.zero:
                f=R[i][c]
                R[i]=[K.sub(a,K.mul(f,b)) for a,b in zip(R[i],R[k])]
                T[i]=[K.sub(a,K.mul(f,b)) for a,b in zip(T[i],T[k])]
        piv_exact.append(c);k+=1
        if k==r:break
    assert k==r
    relations=[]
    for j,original in enumerate(matrix):
        row=original[:];coeff=[K.zero]*r
        for i,c in enumerate(piv_exact):
            f=row[c]
            if f!=K.zero:
                row=[K.sub(a,K.mul(f,b)) for a,b in zip(row,R[i])]
                coeff=[K.add(a,K.mul(f,b)) for a,b in zip(coeff,T[i])]
        assert all(a==K.zero for a in row), 'modular rank failed to span characteristic-zero q'
        # Independently multiply the final saved row combination, rather than
        # trusting the elimination residual or transformation bookkeeping.
        for c in range(len(mons)):
            acc=K.zero
            for b,src in zip(coeff,chosen):acc=K.add(acc,K.mul(b,matrix[src][c]))
            assert acc==original[c]
        relations.append([list(map(str,a)) for a in coeff])
    packed=[[[list(e),list(map(str,K.element(f[e])))] for e in sorted(f)] for f in chart.q]
    out=dict(schema='spur-q-cyclotomic-basis-v1',d=d,chart=[0,1],seed=20261102,
        phi=list(chart.cyclotomic),q_labels=[list(q) for q in chart.labels],
        q_scaling='uniform d+1; same basis and relations for original unscaled q',
        q_model_sha256=hashlib.sha256(json.dumps(packed,separators=(',',':')).encode()).hexdigest(),
        raw_q_indices=chosen,basis_q_labels=[list(chart.labels[i]) for i in chosen],
        rank=r,relations=relations,
        independence=dict(prime=p,omega=omega,monomial_columns=piv,
            monomial_exponents=[list(mons[c]) for c in piv],determinant=minor),
        coefficientwise_spanning_identities_verified=True,
        seconds=round(time.monotonic()-start,6),python=sys.version)
    return out


def verify_saved(path):
    """Read-only coefficient check of the saved identities and rank minor."""
    start=time.monotonic();raw=path.read_bytes();saved=json.loads(raw)
    assert saved['schema']=='spur-q-cyclotomic-basis-v1'
    d=saved['d'];assert d in (6,7) and saved['chart']==[0,1]
    chart=build_chart(d,0,1);K=Field(chart.cyclotomic);mons=list(chart.support)
    assert list(chart.cyclotomic)==({6:[1,-1,1],7:[1,1,1,1,1,1,1]}[d])
    assert saved['phi']==list(chart.cyclotomic)
    assert saved['q_labels']==[list(q) for q in chart.labels]
    packed=[[[list(e),list(map(str,K.element(f[e])))] for e in sorted(f)] for f in chart.q]
    model_sha=hashlib.sha256(json.dumps(packed,separators=(',',':')).encode()).hexdigest()
    assert model_sha==saved['q_model_sha256']
    chosen=saved['raw_q_indices'];r=saved['rank']
    assert len(chosen)==len(set(chosen))==r==(12 if d==6 else 15)
    assert all(isinstance(j,int) and 0<=j<len(chart.q) for j in chosen)
    assert saved['basis_q_labels']==[list(chart.labels[j]) for j in chosen]
    matrix=[[K.element(f.get(e,K.zero)) for e in mons] for f in chart.q]
    relations=saved['relations'];assert len(relations)==len(matrix)
    for original,row in zip(matrix,relations):
        assert len(row)==r and all(len(a)==K.k for a in row)
        coefficients=[K.element(list(map(Q,a))) for a in row]
        for c,expected in enumerate(original):
            actual=K.zero
            for a,j in zip(coefficients,chosen):actual=K.add(actual,K.mul(a,matrix[j][c]))
            assert actual==expected,'saved q spanning identity is false'
    witness=saved['independence'];p=witness['prime'];omega=witness['omega']
    # Trial division suffices here (p=30241), keeping the rank witness self-contained.
    assert p>2 and all(p%j for j in range(2,isqrt(p)+1))
    assert pow(omega,d,p)==1 and all(pow(omega,k,p)!=1 for k in range(1,d))
    assert sum(int(a)*pow(omega,j,p) for j,a in enumerate(chart.cyclotomic))%p==0
    columns=witness['monomial_columns'];assert len(columns)==len(set(columns))==r
    assert all(isinstance(c,int) and 0<=c<len(mons) for c in columns)
    assert witness['monomial_exponents']==[list(mons[c]) for c in columns]
    def reduce_at(a):
        return sum(x.numerator*pow(x.denominator,-1,p)*pow(omega,j,p)
                   for j,x in enumerate(a))%p
    determinant=det_mod([[reduce_at(matrix[j][c]) for c in columns] for j in chosen],p)
    assert determinant==witness['determinant']!=0
    assert path.read_bytes()==raw,'basis certificate changed during read-only check'
    return dict(schema='spur-q-basis-replay-v1',d=d,passed=True,rank=r,
        raw_q_indices=chosen,coefficient_identities_checked=len(matrix)*len(mons),
        prime=p,determinant=determinant,basis_file=path.name,
        basis_sha256=hashlib.sha256(raw).hexdigest(),q_model_sha256=model_sha,
        seconds=round(time.monotonic()-start,6),python=sys.version)


def main():
    if not __debug__:raise RuntimeError('optimized Python disables certificate assertions')
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--d',type=int,choices=[6,7])
    ap.add_argument('--p',type=int,default=30241)
    ap.add_argument('--verify',type=Path,help='verify saved certificate without changing it')
    ap.add_argument('--output',type=Path);args=ap.parse_args()
    if args.verify:
        assert args.d is None,'--verify reads d from the saved certificate'
        out=verify_saved(args.verify)
        if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
        print(json.dumps(out,indent=2),flush=True)
        return
    assert args.d is not None,'provide --d or --verify'
    out=generate(args.d,args.p)
    target=H/f'e43_d{args.d}_q_basis.json';target.write_text(json.dumps(out,indent=2)+'\n')
    assert target.stat().st_size<1024**2
    print(json.dumps({k:v for k,v in out.items() if k!='relations'},indent=2),flush=True)


if __name__=='__main__':main()
