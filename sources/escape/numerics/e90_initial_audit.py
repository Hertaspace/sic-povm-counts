#!/usr/bin/env python3
"""Independent audit of every e04/e05 initial polynomial and torus result.

Uses literal matrices from e90_support_audit, six-digit unramified arithmetic,
and Teichmueller iteration rather than e05's four-digit Newton lift. Every
initial generator is compared as a finite-field polynomial. A separate std
run recomputes the result from the independently generated polynomials.
Writes only e90_*; no helper modules are compiled to __pycache__.
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
import sys
sys.dont_write_bytecode=True
import ast
from pathlib import Path
import hashlib
import itertools
import json
import re
import time
from e90_support_audit import (Algebra,finite_algebra,make_matrices,structure_constants,
                              minor_polynomials,square_polynomials,field_header,run_singular)

HERE=Path(__file__).resolve().parent

def valuation_integer(a,p):
    assert a
    v=0
    while a%p==0:a//=p;v+=1
    return v

class Polynomial:
    def __init__(self,F,terms=None):self.F=F;self.terms=terms or {}
    def coerce(self,value):
        if isinstance(value,Polynomial):return value
        c=self.F.reduce([value]);return Polynomial(self.F,{():c} if c!=self.F.zero else {})
    def __add__(self,other):
        other=self.coerce(other);out=dict(self.terms)
        for key,c in other.terms.items():
            v=self.F.add(out.get(key,self.F.zero),c)
            if v==self.F.zero:out.pop(key,None)
            else:out[key]=v
        return Polynomial(self.F,out)
    __radd__=__add__
    def __neg__(self):return Polynomial(self.F,{k:self.F.neg(c) for k,c in self.terms.items()})
    def __sub__(self,other):return self+-self.coerce(other)
    def __rsub__(self,other):return self.coerce(other)+-self
    def __mul__(self,other):
        other=self.coerce(other);out=Polynomial(self.F)
        for k,c in self.terms.items():
            for l,e in other.terms.items():
                v=self.F.mul(c,e)
                if v!=self.F.zero:out=out+Polynomial(self.F,{tuple(sorted(k+l)):v})
        return out
    __rmul__=__mul__
    def __pow__(self,n):
        result=self.coerce(1);base=self
        while n:
            if n&1:result=result*base
            base=base*base;n>>=1
        return result
    def __eq__(self,other):return self.terms==self.coerce(other).terms

def parse_polynomial(text,F,n):
    env={f'z{q}':Polynomial(F,{(f'z{q}',):F.one}) for q in range(n)}
    env.update({s:Polynomial(F,{(s,):F.one}) for s in ['t','y']})
    env['w']=Polynomial(F,{():F.reduce([0,1])})
    return eval(text.replace('^','**'),{'__builtins__':{}},env)

def local_context(d,p):
    exact=Algebra({3:[1,1,1],4:[1,0,0,0,1],5:[1,1,1,1,1],6:[1,0,-1,0,1]}[d])
    F,residue=finite_algebra(d,p);L=Algebra(F.f,p**6)
    root=L.reduce(residue);q=p**F.n
    for _ in range(6):root=L.power(root,q)
    order=d if d%2 else 2*d
    assert L.power(root,order)==L.one
    assert tuple(x%p for x in root)==residue
    def lead(c):
        if c==exact.zero:return None
        value=L.zero
        for a in reversed(c):value=L.add(L.mul(value,root),L.reduce([a]))
        assert value!=L.zero,'coefficient needs more than six p-adic digits'
        v=0
        while all(x%p==0 for x in value):value=tuple(x//p for x in value);v+=1
        return 2*v,tuple(x%p for x in value)
    return exact,F,root,lead

def independent_initials(row):
    d,p=row['d'],row['p'];n=d*d;mask=row['representative_mask'];weights=row['weights']
    E,F,localroot,lead=local_context(d,p)
    tau=E.reduce([0,1]);mats=make_matrices(d,E,tau)
    constants=structure_constants(d,E,tau,mats)
    minors=minor_polynomials(d,E,mats,True)
    convolution=square_polynomials(d,E,constants,True)[1:]
    first=min(q for q in range(1,n) if mask>>q&1)
    def variable(q):return '1' if q==first else f'z{q}'
    def term_text(key,c):return F.text(c)+'*'+'*'.join(variable(q) for q in key)
    gens=[];minimum_counts=[];valuation_hist={}
    for index,poly in enumerate(minors+convolution):
        terms=[]
        for key,c in sorted(poly.items()):
            v,a=lead(c);valuation_hist[v]=valuation_hist.get(v,0)+1
            terms.append((v+sum(weights[q] for q in key),key,a))
        if not terms:continue
        low=min(v for v,_,_ in terms);leaders=[(key,c) for v,key,c in terms if v==low]
        gens.append('+'.join(term_text(key,c) for key,c in leaders))
        if index>=len(minors):minimum_counts.append(len(leaders))
    seen=set()
    for q in range(1,n):
        if q in seen:continue
        u,v=divmod(q,d);s=(-u%d)*d+(-v%d);seen.update([q,s])
        r,c=constants[q,s];assert r==0
        valuation,coefficient=lead(c);assert valuation==0
        assert weights[q]+weights[s]==row['mu']
        gens.append(term_text((q,s),coefficient)+'-t')
    ord_p=valuation_integer(d+1,p);unit=(d+1)//p**ord_p
    assert 2*weights[0]==2*ord_p+row['mu']
    gens+=['z0^2-'+str(unit)+'*t','t*y-1']
    assert unit%p!=0  # t invertible now forces z0 and every z_q invertible.
    return gens,F,first,dict(minimum_counts=minimum_counts,coefficient_valuation_histogram=valuation_hist,
                             local_root_mod_p6=list(localroot),trace_unit=unit,trace_weight=weights[0])

def target_initial_function():
    path=HERE/'e05_initial_forms.py';tree=ast.parse(path.read_text())
    nodes=[node for node in tree.body if isinstance(node,(ast.ClassDef,ast.FunctionDef))
           and node.name in {'Ring','rings','initial_equations'}]
    assert len(nodes)==3
    namespace={'itertools':itertools}
    exec(compile(ast.Module(body=nodes,type_ignores=[]),str(path),'exec'),namespace)
    return namespace['initial_equations']

def main():
    started=time.monotonic();target=target_initial_function();results=[]
    rows=json.loads((HERE/'e04_weighted_screen.json').read_text())['results']
    expected=json.loads((HERE/'e05_initial_forms.json').read_text())['results']
    oldmap={(r['d'],r['p'],r['representative_mask']):r for r in expected}
    log=['seed=20261031; exact cyclotomic coefficients; independent p^6 Teichmueller lift',
         'initial_d3_bug_fixed: w(z0)=3; trace_unit=1; full torus follows from products and trace',
         'std first attempted for all 12 cases; d6p7 mask1056968640 stopped at 5s by exact own PID; use slimgb for that case']
    for row in rows:
        d,p=row['d'],row['p'];n=d*d;mask=row['representative_mask']
        independent,F,first,details=independent_initials(row)
        actual,actual_first,_=target(row);assert first==actual_first and len(actual)==len(independent)
        for index,(left,right) in enumerate(zip(actual,independent)):
            assert parse_polynomial(left,F,n)==parse_polynomial(right,F,n),(d,p,mask,index,left,right)
        assert not row['violations'] and min(details['minimum_counts'])==row['min_leader_count']
        names=['y','t']+[f'z{q}' for q in range(n) if q!=first]
        algorithm='slimgb' if (d,p,mask)==(6,7,1056968640) else 'std'
        source=field_header(d,p,names)+'ideal I='+','.join(independent)+f';\nideal G={algorithm}(I);\n"RESULT",dim(G),vdim(G),size(G);\nquit;\n'
        stem=f'e90_initial_d{d}_p{p}_m{mask}'
        (HERE/(stem+'.sing')).write_text(source)
        output,seconds,peak=run_singular(source)
        (HERE/(stem+'.out')).write_text(output)
        match=re.search(r'RESULT\s+(-?\d+)\s+(-?\d+)\s+(\d+)',output);assert match,output
        dim,length,basis=map(int,match.groups());old=oldmap[d,p,mask]
        assert (dim,length)==(old['initial_dim'],old['initial_length']),(d,p,mask,dim,length,old)
        record=dict(d=d,p=p,mask=mask,initial_dim=dim,initial_length=length,basis_size=basis,algorithm=algorithm,
                    generators_compared=len(independent),seconds=seconds,peak_rss_bytes=peak,
                    source_sha256=hashlib.sha256(source.encode()).hexdigest(),**details)
        results.append(record);line=json.dumps(record,sort_keys=True);log.append(line);print(line,flush=True)
        (HERE/'e90_initial_audit.json').write_text(json.dumps(dict(results=results),indent=2)+'\n')
        (HERE/'e90_initial_audit.out').write_text('\n'.join(log)+'\n')
    log.append('ALL_CHECKS_PASS; elapsed_seconds='+str(round(time.monotonic()-started,6)))
    (HERE/'e90_initial_audit.out').write_text('\n'.join(log)+'\n');print(log[-1])

if __name__=='__main__':main()
