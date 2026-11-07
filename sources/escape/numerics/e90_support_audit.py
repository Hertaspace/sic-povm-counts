#!/usr/bin/env python3
"""Independent exact audit of e01--e03, writing only e90_*.

Build the Weyl matrices literally, multiply matrices to obtain cocycles,
generate every minor, enumerate recursively, and use every determinant-one
matrix for orbit closure. Recompute all 508 Segre strata with new polynomial
generation. Singular children run serially, <=5 seconds, with own-PID RSS
monitoring and a 6 GiB stop (2 GiB margin). No random arithmetic is used.
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
import ctypes
import hashlib
import itertools
import json
import os
import platform
import re
import subprocess
import time

HERE=Path(__file__).resolve().parent
CASES=[(3,2),(4,5),(5,2),(5,3),(6,7)]

class Algebra:
    def __init__(self,modulus,characteristic=None):
        self.f=tuple(modulus); self.n=len(modulus)-1; self.p=characteristic
        self.zero=(0,)*self.n; self.one=(1,)+(0,)*(self.n-1)
    def reduce(self,values):
        a=list(values)+[0]*max(0,self.n-len(values))
        while len(a)>self.n:
            x=a.pop(); offset=len(a)-self.n
            for i in range(self.n): a[offset+i]-=x*self.f[i]
        return tuple(x%self.p if self.p else x for x in a)
    def add(self,a,b): return self.reduce([x+y for x,y in itertools.zip_longest(a,b,fillvalue=0)])
    def neg(self,a): return tuple(-x%self.p if self.p else -x for x in a)
    def sub(self,a,b): return self.add(a,self.neg(b))
    def mul(self,a,b):
        a=self.reduce(a);b=self.reduce(b);c=[0]*(2*self.n-1)
        for i in range(self.n):
            for j in range(self.n):c[i+j]+=a[i]*b[j]
        return self.reduce(c)
    def power(self,a,k):
        r=self.one
        while k:
            if k&1:r=self.mul(r,a)
            a=self.mul(a,a);k>>=1
        return r
    def inverse(self,a):return self.power(a,self.p**self.n-2)
    def text(self,a):
        return '('+('+'.join(str(x)+(f'*w^{i}' if i else '') for i,x in enumerate(a) if x) or '0')+')'

def finite_algebra(d,p):
    f={3:[1,1,1],4:[2,0,1],5:[1,1,1,1,1],6:[1,0,1]}[d]
    F=Algebra(f,p); tau=F.reduce([0,3 if d==6 else 1])
    n=d if d%2 else 2*d
    assert F.power(tau,n)==F.one
    assert all(F.power(tau,k)!=F.one for k in range(1,n))
    # This test also verifies that the chosen quotient is a field.
    for c in itertools.product(range(p),repeat=F.n):
        if c!=F.zero:assert F.mul(c,F.inverse(c))==F.one
    return F,tau

def make_matrices(d,A,tau):
    omega=A.mul(tau,tau); mats=[]
    for u in range(d):
        for v in range(d):
            matrix=[[A.zero for j in range(d)] for i in range(d)]
            scalar=A.power(tau,u*v)
            for j in range(d):
                matrix[(j+u)%d][j]=A.mul(scalar,A.power(omega,v*j))
            mats.append(matrix)
    return mats

def matrix_multiply(a,b,A):
    n=len(a); out=[[A.zero for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            for k in range(n):out[i][j]=A.add(out[i][j],A.mul(a[i][k],b[k][j]))
    return out

def structure_constants(d,A,tau,mats):
    # Weyl matrices are monomial. Determine each scalar from the first column,
    # then verify every column of the literal matrix product.
    out={}
    for q in range(d*d):
        u,v=divmod(q,d)
        for s in range(d*d):
            x,y=divmod(s,d); r=((u+x)%d)*d+(v+y)%d
            k=(u+x)%d
            product_first=A.mul(mats[q][k][x],mats[s][x][0])
            target=mats[r][k][0]
            inverse=A.power(target,(d if d%2 else 2*d)-1)
            c=A.mul(product_first,inverse)
            for j in range(d):
                k=(u+x+j)%d
                actual=A.mul(mats[q][k][(x+j)%d],mats[s][(x+j)%d][j])
                assert actual==A.mul(c,mats[r][k][j])
            out[q,s]=(r,c)
    return out

def add_term(poly,key,value,A):
    value=A.add(poly.get(key,A.zero),value)
    if value==A.zero:poly.pop(key,None)
    else:poly[key]=value

def minor_polynomials(d,A,mats,include_zero):
    entries=[[[(q,mats[q][i][j]) for q in range(0 if include_zero else 1,d*d)
               if mats[q][i][j]!=A.zero] for j in range(d)] for i in range(d)]
    polys=[]
    for i,k in itertools.combinations(range(d),2):
        for j,l in itertools.combinations(range(d),2):
            poly={}
            for left,right,negative in [(entries[i][j],entries[k][l],False),
                                         (entries[i][l],entries[k][j],True)]:
                for q,c in left:
                    for r,e in right:
                        value=A.mul(c,e)
                        if negative:value=A.neg(value)
                        add_term(poly,tuple(sorted((q,r))),value,A)
            polys.append(poly)
    return polys

def square_polynomials(d,A,constants,include_zero):
    polys=[{} for _ in range(d*d)]
    for q in range(0 if include_zero else 1,d*d):
        for s in range(0 if include_zero else 1,d*d):
            r,c=constants[q,s]
            add_term(polys[r],tuple(sorted((q,s))),c,A)
    if include_zero:
        for r in range(d*d):add_term(polys[r],tuple(sorted((0,r))),A.reduce([-d]),A)
    return polys

def monomials(poly):return sorted((1<<q)|(1<<r) for q,r in poly)
def opposite(q,d):u,v=divmod(q,d);return (-u%d)*d+(-v%d)
def phase_formula(q,s,d):
    u,v=divmod(q,d);x,y=divmod(s,d)
    return (u*v+x*y+2*v*x-((u+x)%d)*((v+y)%d))%(d if d%2 else 2*d)

def rss(pid):
    return resident_bytes(pid)
def run_singular(source,timeout=5):
    command=['Singular','--no-rc','--random=20261031','--cpus=1','--threads=1','--flint-threads=1','-q']
    child=subprocess.Popen(command,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
                           text=True,cwd=HERE,env=dict(os.environ,OMP_NUM_THREADS='1',TMPDIR=str(HERE)))
    started=time.monotonic(); first=True; peak=0
    while True:
        try:
            output,_=child.communicate(source if first else None,timeout=0.025);break
        except subprocess.TimeoutExpired:
            first=False;peak=max(peak,rss(child.pid))
            if peak>=6*1024**3 or time.monotonic()-started>timeout:
                child.kill();output,_=child.communicate()
                raise RuntimeError('own Singular child stopped: '+output[-1000:])
    if child.returncode or re.search(r'^\s*\?',output,re.M):raise RuntimeError(output)
    return output,round(time.monotonic()-started,6),peak

def field_header(d,p,names):
    f={3:'w^2+w+1',4:'w^2+2',5:'w^4+w^3+w^2+w+1',6:'w^2+1'}[d]
    return f'ring R=({p},w),({",".join(names)}),dp;\nminpoly={f};\n'

def stratum_source(d,p,mask,F,polys):
    support=[q for q in range(1,d*d) if mask>>q&1]; first=support[0]
    names=[f'z{q}' for q in support[1:]]+['h']
    gens=[]
    for poly in polys:
        terms=[]
        for (q,r),c in sorted(poly.items()):
            if mask>>q&1 and mask>>r&1:
                factors=[F.text(c)]+[f'z{x}' for x in (q,r) if x!=first]
                terms.append('*'.join(factors))
        if terms:gens.append('+'.join(terms))
    gens.append('h*'+'*'.join(f'z{q}' for q in support[1:])+'-1')
    return field_header(d,p,names)+'ideal I='+','.join(gens)+';\nideal G=slimgb(I);\n"RESULT",dim(G),vdim(G),size(G);\nquit;\n'

def main():
    started=time.monotonic();log=[];all_records=[];censuses=[]
    log.append('seed=20261031; independent exact finite quotient arithmetic; no floating point')
    log.append('python='+platform.python_version()+' platform='+platform.platform())
    log.append('Singular=4.4.1; full SL2 enumeration; all 508 strata rerun; timeout=5s; RSS stop=6GiB')
    source=HERE/'e90_support_audit.cpp';exe=HERE/'e90_support_audit.bin'
    subprocess.run([executable('c++'),'-O3','-std=c++17',str(source),'-o',str(exe)],check=True)
    expected_rows=json.loads((HERE/'e03_support_strata.json').read_text())['rows']
    for d,p in CASES:
        F,tau=finite_algebra(d,p);mats=make_matrices(d,F,tau)
        constants=structure_constants(d,F,tau,mats)
        for (q,s),(r,c) in constants.items():assert c==F.power(tau,phase_formula(q,s,d))
        minors=minor_polynomials(d,F,mats,False)
        square=square_polynomials(d,F,constants,False)
        original=(HERE/f'e02_minors_d{d}_p{p}.txt').read_text().splitlines()
        expected=[list(map(int,line.split()[1:])) for line in original[1:]]
        assert [monomials(poly) for poly in minors if poly]==expected
        lines=[str(d)]
        for family in (square[1:],minors):
            nonzero=[poly for poly in family if poly];lines.append(str(len(nonzero)))
            for poly in nonzero:
                row=monomials(poly);lines.append(str(len(row))+' '+' '.join(map(str,row)))
        input_text='\n'.join(lines)+'\n'
        (HERE/f'e90_support_d{d}_p{p}.txt').write_text(input_text)
        result=subprocess.run([str(exe)],input=input_text,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
                              text=True,check=True,timeout=30)
        (HERE/f'e90_census_d{d}_p{p}.out').write_text(result.stdout)
        lines=result.stdout.splitlines();counts=list(map(int,lines[0].split()[1:]))
        keys=['opposite_pairs','sl2_order','size_at_least_d','square_survivors','raw_minor_survivors',
              'square_orbits','closed_minor_survivors','closed_minor_orbits']
        census=dict(d=d,p=p,**dict(zip(keys,counts)))
        reps=[tuple(map(int,line.split()[1:])) for line in lines[1:]]
        expected_case=[r for r in expected_rows if (r['d'],r['p'])==(d,p)]
        expected_reps=sorted((r['representative_mask'],r['size'],r['support_size']) for r in expected_case)
        assert reps==expected_reps,(d,p,'representative mismatch')
        oldmap={r['representative_mask']:r for r in expected_case}
        for mask,size,support_size in reps:
            src=stratum_source(d,p,mask,F,minors)
            (HERE/'e90_stratum_last.sing').write_text(src)
            output,seconds,peak=run_singular(src)
            match=re.search(r'RESULT\s+(-?\d+)\s+(-?\d+)\s+(\d+)',output)
            assert match,output
            dim,length,basis=map(int,match.groups());old=oldmap[mask]
            assert (dim,length)==(old['dim'],old['length']),(d,p,mask,dim,length,old)
            record=dict(d=d,p=p,mask=mask,orbit_size=size,support_size=support_size,dim=dim,length=length,
                        seconds=seconds,peak_rss_bytes=peak,source_sha256=hashlib.sha256(src.encode()).hexdigest())
            all_records.append(record)
        nonempty=[r for r in all_records if (r['d'],r['p'])==(d,p) and r['dim']>=0]
        census.update(nonempty_orbits=len(nonempty),nonempty_supports=sum(r['orbit_size'] for r in nonempty))
        censuses.append(census);line=json.dumps(census,sort_keys=True);log.append(line);print(line,flush=True)
        (HERE/'e90_support_audit.json').write_text(json.dumps(dict(censuses=censuses,strata=all_records),indent=2)+'\n')
        (HERE/'e90_support_audit.out').write_text('\n'.join(log)+'\n')
    log.append('ALL_CHECKS_PASS; elapsed_seconds='+str(round(time.monotonic()-started,6)))
    (HERE/'e90_support_audit.out').write_text('\n'.join(log)+'\n');print(log[-1])

if __name__=='__main__':main()
