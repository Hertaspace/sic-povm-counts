#!/usr/bin/env python3
"""Exact backtracking of prime-field lex GB into a specified finite field.

No floating point. Complete if the resulting distinct points equal vdim(H).
Usage: e03_solve.py d p modulus(comma-separated,low-to-high) [e01|e04]
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
import json, re, sys, time, platform
from e02_groups import GF

ROOT=Path(__file__).resolve().parents[1]
def parse_poly(s,names,p):
    terms=[]
    for t in re.findall(r'[+-]?[^+-]+',s.replace(' ','')):
        sign=-1 if t.startswith('-') else 1
        t=t.lstrip('+-'); c=sign; exps=[0]*len(names)
        for factor in t.split('*'):
            if re.fullmatch(r'\d+',factor): c*=int(factor)
            elif factor:
                v,sep,e=factor.partition('^'); exps[names.index(v)]+=int(e) if sep else 1
        c%=p
        if c: terms.append((c,tuple(exps)))
    return terms

def split_terms(s):
    depth=0;start=0;out=[]
    for i,c in enumerate(s):
        if c=='(':depth+=1
        if c==')':depth-=1
        if i and c in '+-' and depth==0:out.append(s[start:i]);start=i
    out.append(s[start:]);return out

def parse_number(s,F,u_code=None):
    u_code=F.p if u_code is None else u_code
    if s.startswith('(') and s.endswith(')'):s=s[1:-1]
    val=0
    for t in split_terms(s):
        sign=-1 if t.startswith('-') else 1;t=t.lstrip('+-');c=F.scalar(sign)
        for factor in t.split('*'):
            if factor.startswith('u'):
                e=int(factor.partition('^')[2] or 1);c=F.mul(c,F.pow(u_code,e))
            else:c=F.mul(c,F.scalar(int(factor)))
        val=F.add(val,c)
    return val

def parse_extension_poly(s,names,F,u_code=None):
    out=[]
    for t in split_terms(s.replace(' ','')):
        sign=-1 if t.startswith('-') else 1;t=t.lstrip('+-');c=F.scalar(sign);es=[0]*len(names)
        depth=0;factors=[];start=0
        for i,ch in enumerate(t):
            if ch=='(':depth+=1
            if ch==')':depth-=1
            if ch=='*' and depth==0:factors.append(t[start:i]);start=i+1
        factors.append(t[start:])
        for factor in factors:
            name,sep,e=factor.partition('^')
            if name in names:es[names.index(name)]+=int(e) if sep else 1
            else:c=F.mul(c,parse_number(factor,F,u_code))
        if c:out.append((c,tuple(es)))
    return out

def eval_poly(poly,values,F):
    acc=0
    for c,es in poly:
        term=c
        for x,e in zip(values,es):
            if e: term=F.mul(term,F.pow(x,e))
        acc=F.add(acc,term)
    return acc

def enumerate_lex(polys,names,F,verbose=True):
    n=len(names); by_var=[[] for _ in names]
    for poly in polys:
        first=min(i for c,es in poly for i,e in enumerate(es) if e)
        by_var[first].append(poly)
    vals=[0]*n; solutions=[]; counts=[0]*n
    # Only field-root enumeration, no unverified factorization over GF(q).
    def rec(i):
        if i<0:
            assert all(eval_poly(poly,vals,F)==0 for poly in polys)
            solutions.append(vals.copy());return
        unis=[]
        for poly in by_var[i]:
            deg=max(es[i] for _,es in poly); cf=[0]*(deg+1)
            for c,es in poly:
                for j in range(i+1,n):
                    if es[j]: c=F.mul(c,F.pow(vals[j],es[j]))
                cf[es[i]]=F.add(cf[es[i]],c)
            while cf and cf[-1]==0:cf.pop()
            if cf:
                if len(cf)==1:return
                unis.append(cf)
        unis.sort(key=len)
        def ev(cf,x):
            a=0
            for c in cf[::-1]:a=F.add(F.mul(a,x),c)
            return a
        if not unis: candidates=range(F.q)
        elif len(unis[0])==2:
            f=unis[0]; candidates=[F.mul(F.sub(0,f[0]),F.inv(f[1]))]
        else:candidates=range(F.q)
        for x in candidates:
            if all(ev(f,x)==0 for f in unis):
                vals[i]=x;counts[i]+=1;rec(i-1)
    rec(n-1)
    if verbose:print('branch_counts',dict(zip(names,counts)),flush=True)
    return solutions

def main():
    d,p=map(int,sys.argv[1:3]); modulus=list(map(int,sys.argv[3].split(',')))
    prefix=sys.argv[4] if len(sys.argv)>4 else 'e01'; F=GF(p,modulus)
    source=ROOT/'numerics'/f'{prefix}_d{d}_p{p}.singular.out'
    raw=source.read_text(); lex=raw.split('BEGIN_LEX\n')[1].split('END_LEX')[0]
    names=['y','t']+[f'b{i}' for i in range(1,d)]+[f'a{i}' for i in range(1,d)]
    polys=[parse_poly(s.split('=',1)[1],names,p) for s in lex.splitlines() if re.match(r'J\[\d+\]=',s)]
    expected=int(re.search(r'NULL_LENGTH\s+(\d+)',raw).group(1))
    start=time.monotonic(); rows=enumerate_lex(polys,names,F)
    points=[]
    for row in rows:
        points.append([[1]+row[d+1:],[1]+row[2:d+1]])
        assert len(points[-1][0])==len(points[-1][1])==d
    result={'d':d,'p':p,'modulus':modulus,'q':F.q,'source':str(source.relative_to(ROOT)),
            'seed':20261031,'arithmetic':'exact finite field','python':platform.python_version(),
            'expected_length_trace_zero_chart':expected,'distinct_chart_points':len(points),
            'complete_reduced_chart':len(points)==expected,'points':points,
            'elapsed':time.monotonic()-start}
    dest=ROOT/'numerics'/f'e03_d{d}_p{p}_q{F.q}.json';dest.write_text(json.dumps(result,indent=2))
    print({k:v for k,v in result.items() if k!='points'},flush=True)
if __name__=='__main__':main()
