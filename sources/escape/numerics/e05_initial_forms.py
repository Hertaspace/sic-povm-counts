#!/usr/bin/env python3
"""Joint initial equations for the explicit e04 three-level weights.

NOT the initial ideal of the whole SIC ideal, and NOT an exhaustive weight
search. A unit standard basis excludes this particular weight. Polynomial
coefficients are reduced exactly in Z[tau]; p-adic leading coefficients use
an unramified ring modulo p^4, with v(p)=2 and pi^2=p.
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
from collections import defaultdict
import ctypes
import itertools
import json
import os
import re
import resource
import subprocess
import time

HERE=Path(__file__).resolve().parent

class Ring:
    def __init__(self,modulus,mod=None):self.f=modulus;self.n=len(modulus)-1;self.mod=mod
    def norm(self,a):
        a=list(a)+[0]*max(0,self.n-len(a))
        for i in range(len(a)-1,self.n-1,-1):
            for j in range(self.n):a[i-self.n+j]-=a[i]*self.f[j]
        a=a[:self.n]
        return tuple(x%self.mod if self.mod else x for x in a)
    def add(self,a,b):return self.norm([x+y for x,y in itertools.zip_longest(a,b,fillvalue=0)])
    def neg(self,a):return self.norm([-x for x in a])
    def mul(self,a,b):
        c=[0]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):c[i+j]+=x*y
        return self.norm(c)
    def power(self,a,n):
        b=self.norm([1])
        while n:
            if n&1:b=self.mul(b,a)
            a=self.mul(a,a);n//=2
        return b
    def inverse(self,a,p):
        # Start with the finite-field inverse and apply Newton lifting.
        b=self.power(a,p**self.n-2)
        for _ in range(5):b=self.mul(b,self.add((2,),self.neg(self.mul(a,b))))
        assert self.mul(a,b)==self.norm([1])
        return b

def rings(d,p):
    phi={3:[1,1,1],4:[1,0,0,0,1],5:[1,1,1,1,1],6:[1,0,-1,0,1]}[d]
    exact=Ring(phi);order=d if d%2 else 2*d
    if d in (3,5):local=Ring(phi,p**4);root=local.norm([0,1])
    else:
        local=Ring([2,0,1] if d==4 else [1,0,1],p**4)
        root=local.norm([0,1 if d==4 else 3])
        for _ in range(5):
            residual=local.add(local.power(root,order),(-1,))
            derivative=local.mul((order,),local.power(root,order-1))
            root=local.add(root,local.neg(local.mul(residual,local.inverse(derivative,p))))
    assert local.power(root,order)==local.norm([1])
    return exact,local,root,order

def initial_equations(row,return_polynomials=False):
    d,p=row['d'],row['p'];weights=row['weights'];n=d*d
    E,L,root,order=rings(d,p)
    powers=[E.power((0,1),e) for e in range(order)]
    def lead(c):
        if not any(c):return None
        a=L.norm([0])
        for x in reversed(c):a=L.add(L.mul(a,root),(x,))
        k=0
        while all(x%p==0 for x in a):
            a=tuple(x//p for x in a);k+=1
            if k>=4:raise ValueError('insufficient p-adic precision')
        return 2*k,tuple(x%p for x in a)
    def entry(i,j):
        u=(i-j)%d
        return [(u*d+v,powers[(u*v+2*v*j)%order]) for v in range(d)]
    polynomials=[]
    for i,k in itertools.combinations(range(d),2):
        for j,l in itertools.combinations(range(d),2):
            poly={}
            for sign,aa,bb in [(1,entry(i,j),entry(k,l)),(-1,entry(i,l),entry(k,j))]:
                for (q,c),(r,cc) in itertools.product(aa,bb):
                    key=tuple(sorted((q,r)));a=E.mul(c,cc)
                    if sign<0:a=E.neg(a)
                    poly[key]=E.add(poly.get(key,(0,)),a)
            polynomials.append(poly)
    for r in range(1,n):
        poly={(0,r):E.norm([2-d])};u,v=divmod(r,d)
        for q in range(1,n):
            x,y=divmod(q,d);s=((u-x)%d)*d+(v-y)%d
            if s==0:continue
            xx,yy=divmod(s,d)
            exponent=(x*y+xx*yy+2*y*xx-u*v)%order
            key=tuple(sorted((q,s)));poly[key]=E.add(poly.get(key,(0,)),powers[exponent])
        polynomials.append(poly)
    if return_polynomials:return polynomials,lead
    out=[]
    def coeffstr(c):return '('+('+'.join(f'{x}*w^{i}' if i else str(x) for i,x in enumerate(c) if x) or '0')+')'
    first=min(q for q in range(1,n) if row['representative_mask']>>q&1)
    def variable(q):return '1' if q==first else f'z{q}'
    for poly in polynomials:
        terms=[]
        for key,c in poly.items():
            info=lead(c)
            if info:terms.append((info[0]+sum(weights[q] for q in key),key,info[1]))
        if not terms:continue
        low=min(x[0] for x in terms)
        out.append('+'.join(coeffstr(c)+'*'+ '*'.join(variable(q) for q in key) for val,key,c in terms if val==low))
    seen=set()
    for q in range(1,n):
        if q in seen:continue
        u,v=divmod(q,d);s=(-u%d)*d+(-v%d);seen.update([q,s]);x,y=divmod(s,d)
        exponent=(u*v+x*y+2*v*x)%order
        c=lead(powers[exponent]);assert c[0]==0
        out.append(coeffstr(c[1])+'*'+variable(q)+'*'+variable(s)+'-t')
    trace_unit=d+1
    while trace_unit%p==0:trace_unit//=p
    out += ['z0^2-'+str(trace_unit)+'*t','t*y-1']
    return out,first,L.f

def resident(pid):
    return resident_bytes(pid)
def main():
  rows=json.loads((HERE/'e04_weighted_screen.json').read_text())['results'];results=[]
  env=dict(os.environ,OMP_NUM_THREADS='1',TMPDIR=str(HERE))
  command=['Singular','--no-rc','--random=20261031','--cpus=1','--threads=1','--flint-threads=1','-q']
  with (HERE/'e05_initial_forms.out').open('w') as log:
    log.write('seed=20261031 exact cyclotomic and unramified p^4 coefficients; pi^2=p; one child; RSS stop 6GiB; timeout 20s\n')
    for row in rows:
        d,p=row['d'],row['p'];gens,first,minimum=initial_equations(row)
        names=['y','t']+[f'z{q}' for q in range(d*d) if q!=first]
        if d==3:poly='w^2+w+1'
        elif d==4:poly='w^2+2'
        elif d==5:poly='w^4+w^3+w^2+w+1'
        else:poly='w^2+1'
        src=f'ring R=({p},w),({",".join(names)}),dp;\nminpoly={poly};\nideal I={",".join(gens)};\nideal G=slimgb(I);\n"RESULT",dim(G),vdim(G),size(G);\nquit;\n'
        stem=f'e05_d{d}_p{p}_s{row["support_size"]}_m{row["representative_mask"]}'
        (HERE/(stem+'.sing')).write_text(src)
        result={k:row[k] for k in ('d','p','size','support_size','representative_mask','dim')};start=time.monotonic();peak=0
        child=subprocess.Popen(command,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,cwd=HERE,env=env)
        firstcall=True;stopped=None
        try:
            while True:
                try:output,_=child.communicate(src if firstcall else None,timeout=.05);break
                except subprocess.TimeoutExpired:
                    firstcall=False;peak=max(peak,resident(child.pid))
                    if peak>=6*1024**3:stopped='memory_stop'
                    elif time.monotonic()-start>=20:stopped='timeout'
                    if stopped:child.kill();output,_=child.communicate();break
        except Exception:
            child.kill();child.communicate();raise
        m=re.search(r'RESULT\s+(-?\d+)\s+(-?\d+)\s+(\d+)',output)
        if stopped:result['status']=stopped
        elif child.returncode==0 and m and not re.search(r'^\s*\?',output,re.M):result.update(status='complete',initial_dim=int(m[1]),initial_length=int(m[2]),initial_basis_size=int(m[3]))
        else:result.update(status='error',output=output[-2000:])
        result.update(seconds=round(time.monotonic()-start,6),sampled_peak_rss_bytes=peak,source=stem+'.sing');results.append(result)
        log.write(json.dumps(result,sort_keys=True)+'\n');log.flush();print(json.dumps(result,sort_keys=True),flush=True)
        (HERE/'e05_initial_forms.json').write_text(json.dumps({'seed':20261031,'results':results},indent=2)+'\n')
    log.write('children_ru_maxrss_bytes='+str(resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)+'\n')

if __name__=='__main__':main()
