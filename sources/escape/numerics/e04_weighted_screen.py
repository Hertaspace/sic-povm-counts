#!/usr/bin/env python3
"""Test every equation (11) for a finite, explicit three-level completion.

Normalize v(p)=2, mu=2, delta=(v(d+1)+2)/2; assign w=0 on S, 2 on -S,
and 1 on all remaining nonzero labels. This is only a witness in the
prevariety of the displayed equations, never a SIC or a lifting witness.
Merge the z0*zr coefficient (2-d) and all unordered pairs first. r=0 is
replaced by the exact trace/member identity after the product equations.
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
import json
import math

HERE=Path(__file__).resolve().parent
def phase(p,q,d):
    u,v=divmod(p,d);x,y=divmod(q,d);r=(u+x)%d;s=(v+y)%d
    return (u*v+x*y+2*v*x-r*s)%(d if d%2 else 2*d)
def vp(a,p):
    if not a:return math.inf
    n=0
    while a%p==0:n+=1;a//=p
    return n
def check(d,p,mask):
    n=d*d;order=d if d%2 else 2*d
    def opposite(q):u,v=divmod(q,d);return (-u%d)*d+(-v%d)
    S={q for q in range(1,n) if mask>>q&1};minus={opposite(q) for q in S}
    delta=vp(d+1,p)+1
    weights=[delta]+[0 if q in S else 2 if q in minus else 1 for q in range(1,n)]
    assert min(weights)==0 and all(weights[q]+weights[opposite(q)]==2 for q in range(1,n))
    violations=[];minimum_counts=[]
    for r in range(1,n):
        terms=[]
        cv=2*vp(2-d,p)
        if cv!=math.inf:terms.append((cv+weights[0]+weights[r],(0,r)))
        u,v=divmod(r,d)
        for q in range(1,n):
            x,y=divmod(q,d);s=((u-x)%d)*d+(v-y)%d
            if s==0 or s<q:continue
            coefficient_value=0
            if q!=s:
                a,b=phase(q,s,d),phase(s,q,d);diff=(a-b)%order
                if order%2==0 and diff==order//2:continue
                if p==2 and diff==0:coefficient_value=2
            terms.append((coefficient_value+weights[q]+weights[s],(q,s)))
        minimum=min(v for v,_ in terms);leaders=[m for v,m in terms if v==minimum]
        minimum_counts.append(len(leaders))
        if len(leaders)==1:violations.append({'label':divmod(r,d),'minimum':minimum,'monomial':leaders[0]})
    return dict(weights=weights,mu=2,v_p=2,delta=delta,min_leader_count=min(minimum_counts),violations=violations)

rows=json.loads((HERE/'e03_support_strata.json').read_text())['rows'];results=[];lines=['seed=20261031 exact integer valuations, all displayed nonzero-r equations (11)']
for row in rows:
    if row['status']!='complete' or row['dim']<0:continue
    result={k:row[k] for k in ('d','p','size','support_size','representative_mask','dim')}
    result.update(check(row['d'],row['p'],row['representative_mask']));results.append(result)
    line=f'd={row["d"]} p={row["p"]} |S|={row["support_size"]} orbit_size={row["size"]} dim={row["dim"]} singleton_violations={len(result["violations"])} min_leaders={result["min_leader_count"]}'
    print(line);lines.append(line)
(HERE/'e04_weighted_screen.out').write_text('\n'.join(lines)+'\n')
(HERE/'e04_weighted_screen.json').write_text(json.dumps({'seed':20261031,'results':results},indent=2)+'\n')
