#!/usr/bin/env python3.14
"""<=4 minute follow-up: opposite-pair elimination + repeated affine forms.
Also fixes the WH-transitive finite minimal support layer to E_(0,-u).
Only joint initial ideals get residue constraints; original polynomials do not.
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
from fractions import Fraction
from collections import Counter
import importlib.util,inspect,json,time
import z3
H=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('e08worker',H/'e08_tropical_cells.py')
W=importlib.util.module_from_spec(sp);sp.loader.exec_module(W)
START=time.monotonic();W.DEADLINE=START+130
OLDINITIAL=W.initial.initial_equations
STATS={}

def augmented(row,return_polynomials=False):
    answer=OLDINITIAL(row,return_polynomials=return_polynomials)
    if return_polynomials:return answer
    gens,first,minimum=answer;d,p=row['d'],row['p'];u=first//d
    support=[q for q in range(1,d*d) if row['representative_mask']>>q&1]
    assert support==list(range(u*d,(u+1)*d))
    _,L,root,_=W.initial.rings(d,p)
    for q in support:
        if q==first:continue
        c=tuple(v%p for v in L.power(root,u*(q%d)))
        txt='+'.join(str(v)+(f'*w^{i}' if i else '') for i,v in enumerate(c) if v) or '0'
        gens.append(f'z{q}-({txt})')
    return gens,first,minimum
W.initial.initial_equations=augmented

def optimized(row):
    polys,lead=OLDINITIAL(row,return_polynomials=True);d=row['d'];n=d*d
    S={q for q in range(1,n) if row['representative_mask']>>q&1}
    def opp(q):u,v=divmod(q,d);return (-u%d)*d+(-v%d)
    neg={opp(q) for q in S};unknown=[q for q in range(1,n) if q not in S|neg and q<=opp(q) and q!=opp(q)]
    mu=z3.Real('mu');free={q:z3.Real(f'u{q}') for q in unknown}
    vars=[mu]+list(free.values());k=len(vars)
    # Last entry is the affine constant, other entries are exact rational coefficients.
    vectors=[]
    for q in range(n):
        vec=[Fraction(0)]*(k+1)
        if q==0:vec[0]=Fraction(1,2);vec[-1]=row['delta']-1
        elif q in S:pass
        elif q in neg:vec[0]=1
        elif q==opp(q):vec[0]=Fraction(1,2)
        elif q in free:vec[1+unknown.index(q)]=1
        else:vec[0]=1;vec[1+unknown.index(opp(q))]=-1
        vectors.append(tuple(vec))
    def linear(vec):return z3.Sum([z3.RealVal(str(v))*x for v,x in zip(vec[:-1],vars) if v]+[z3.RealVal(str(vec[-1]))])
    ws=[linear(v) for v in vectors]
    solver=z3.Solver();solver.set(timeout=30000);solver.add(mu>0)
    for x in free.values():solver.add(x>0,x<mu)
    cached=[];mapping=[];raw=0;forms=0;constraints=0
    for index,poly in enumerate(polys):
        ts=[];count=Counter()
        for mon,c in poly.items():
            info=lead(c)
            if not info:continue
            ts.append((mon,info[0]));vec=[sum(vectors[q][i] for q in mon) for i in range(k+1)];vec[-1]+=info[0];count[tuple(vec)]+=1
        cached.append(ts)
        if ts:mapping.append(index)
        raw+=len(ts);forms+=len(count)
        for vec,multiplicity in count.items():
            if multiplicity>1:continue
            value=linear(vec);other=[linear(v)<=value for v in count if v!=vec]
            solver.add(z3.Or(*other));constraints+=1
    # Existing certified cuts remain valid after adding residue-point conditions.
    previous=sorted(H.glob(f'e08_d{d}_p{row["p"]}_m{row["representative_mask"]}_c??_cut.json'))
    oldws=[z3.Real(f'w{q}') for q in range(n)]
    decls={'mu':mu,**{f'w{q}':oldws[q] for q in range(n)}}
    for path in previous:
        cut=json.loads(path.read_text())
        for expr in z3.parse_smt2_string(cut['cut_smt2'],decls=decls):
            solver.add(z3.substitute(expr,*list(zip(oldws,ws))))
    # Verify finite-layer chosen point against reductions of ALL original polynomials.
    _,L,root,_=W.initial.rings(d,row['p']);F=W.initial.Ring(L.f,row['p']);u=min(S)//d
    point=[F.norm([0]) for _ in range(n)]
    for q in S:point[q]=F.norm(L.power(root,u*(q%d)))
    for poly in polys:
        total=F.norm([0])
        for mon,c in poly.items():
            info=lead(c)
            if not info or info[0]>0:continue
            value=info[1]
            for q in mon:value=F.mul(value,point[q])
            total=F.add(total,value)
        assert not any(total)
    STATS[str(row['representative_mask'])]={'free_opposite_pairs':len(free),'raw_terms':raw,'affine_forms':forms,'singleton_constraints':constraints,'prior_certified_cuts':[p.name for p in previous],'residue_tau':tuple(v%row['p'] for v in root),'residue_support_point_verified_all_original_reductions':True,'special_layer_length':d,'u':u}
    return solver,mu,ws,polys,lead,cached,mapping
W.build=optimized
# Reuse the audited certificate, replay, and cell construction code verbatim,
# changing only artifact namespace and per-support time limit.
source=inspect.getsource(W.run_row).replace("base=f'e08_d", "base=f'e08b_d").replace('per_row=30 if d<6 else 20','per_row=40')
exec(source,W.__dict__)

def main():
    rows=json.loads((H/'e04_weighted_screen.json').read_text())['results']
    targets=[(5,3,992),(6,7,4032),(6,7,258048)]
    result={'seed':20261031,'z3_version':z3.get_version_string(),'results':[],'stats':STATS}
    for target in targets:
        row=next(r for r in rows if (r['d'],r['p'],r['representative_mask'])==target)
        out=W.run_row(row)
        compact={k:v for k,v in out.items() if k!='cuts'};compact['cut_count']=len(out['cuts'])
        result['results'].append(compact);result['seconds']=round(time.monotonic()-START,6)
        W.write_small(H/'e08b_optimized_cells.json',json.dumps(result,indent=2)+'\n')
        print(json.dumps({'SUPPORT_DONE':compact,'stats':STATS[str(row['representative_mask'])]},sort_keys=True),flush=True)
    print('TOTAL_SECONDS',round(time.monotonic()-START,6),flush=True)
if __name__=='__main__':main()
