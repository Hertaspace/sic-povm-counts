#!/usr/bin/env python3.14
"""Finite open-cell exclusion. No SAT weight is called a genuine lifting.
Only e08_* files are written. One Singular child at a time, <=10 sec / 6GiB.
Z3 uses exact LRA, <=30 sec/check, <=2048MiB. Global script limit 220 sec.
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
import ctypes
import importlib.util
import json
import os
import re
import subprocess
import time
import z3

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('e08_initial',HERE/'e05_initial_forms.py')
initial=importlib.util.module_from_spec(spec);spec.loader.exec_module(initial)
z3.set_param('memory_max_size',2048)
z3.set_param('smt.random_seed',20261031)
z3.set_param('sat.random_seed',20261031)
START=time.monotonic();DEADLINE=START+220

def write_small(path,text):
    raw=text.encode()
    if len(raw)<2**20:path.write_text(text);return [path.name]
    # Byte splitting is safe here: SMT2 is ASCII. Rejoin in numeric suffix order.
    out=[]
    for j in range(0,len(raw),900000):
        p=Path(str(path)+f'.part{j//900000:03d}');p.write_bytes(raw[j:j+900000]);out.append(p.name)
    path.write_text((('; Split payload; concatenate in this order: '+','.join(out)+'\n') if path.suffix=='.smt2' else json.dumps({'split_parts':out})+'\n'))
    return out

def singular(src,stem):
    path=HERE/(stem+'.sing');write_small(path,src)
    child=subprocess.Popen(['Singular','--no-rc','--random=20261031','--cpus=1','--threads=1','--flint-threads=1','-q'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,cwd=HERE,env=dict(os.environ,OMP_NUM_THREADS='1',TMPDIR=str(HERE)))
    start=time.monotonic();first=True;peak=0;stop=None
    try:
        while True:
            try:out,_=child.communicate(src if first else None,timeout=.05);break
            except subprocess.TimeoutExpired:
                first=False
                try:peak=max(peak,initial.resident(child.pid))
                except RuntimeError:pass
                if peak>=6*2**30:stop='rss_stop'
                elif time.monotonic()-start>=min(10, max(.1,DEADLINE-start)):stop='timeout'
                if stop:child.kill();out,_=child.communicate();break
    except BaseException:
        child.kill();child.communicate();raise
    files=write_small(HERE/(stem+'.sing.out'),out)
    result={'seconds':round(time.monotonic()-start,6),'sampled_peak_rss':peak,'status':stop or 'complete','returncode':child.returncode,'files':files}
    if re.search(r'^\s*\?',out,re.M):result['status']='error'
    return result,out

def terms(poly,lead,weights):
    out=[]
    for mon,c in poly.items():
        info=lead(c)
        if info:out.append((mon,info[0],sum(weights[q] for q in mon)+info[0]))
    return out

def build(row):
    polys,lead=initial.initial_equations(row,return_polynomials=True)
    d=row['d'];n=d*d;mu=z3.Real('mu');ws=[z3.Real(f'w{q}') for q in range(n)]
    solver=z3.Solver();solver.set(timeout=30000)
    solver.add(mu>0,ws[0]==mu/2+row['delta']-1)
    support={q for q in range(1,n) if row['representative_mask']>>q&1}
    minus={(-q//d) for q in []}
    def opp(q):u,v=divmod(q,d);return (-u%d)*d+(-v%d)
    minus={opp(q) for q in support}
    for q in range(1,n):
        solver.add(ws[q]+ws[opp(q)]==mu)
        if q in support:solver.add(ws[q]==0)
        elif q in minus:solver.add(ws[q]==mu)
        else:solver.add(ws[q]>0,ws[q]<mu)
    cached=[];mapping=[]
    for index,poly in enumerate(polys):
        ts=[]
        for mon,c in poly.items():
            info=lead(c)
            if info:ts.append((mon,info[0]))
        cached.append(ts)
        if ts:mapping.append(index)
        values=[z3.Sum([ws[q] for q in mon])+v for mon,v in ts]
        if len(values)<2:
            if values:solver.add(False)
        else:
            low=z3.Real(f'min{index}')
            solver.add(*[low<=v for v in values],z3.PbGe([(low==v,1) for v in values],2))
    return solver,mu,ws,polys,lead,cached,mapping

def certificate_source(row,gens,first):
    d,p=row['d'],row['p'];names=['y','t']+[f'z{q}' for q in range(d*d) if q!=first]
    minimum={4:'w^2+2',5:'w^4+w^3+w^2+w+1',6:'w^2+1'}[d]
    return f'''ring R=({p},w),({','.join(names)}),dp;
minpoly={minimum};
short=0;
ideal I={','.join(gens)};
ideal G=slimgb(I);
"INIT_RESULT",dim(G),vdim(G),size(G);
if(size(G)==1 && G[1]==1){{
  ideal J=1;
  matrix U=lift(I,J);
  poly Verify=0;
  int i;
  for(i=1;i<=nrows(U);i++){{Verify=Verify+I[i]*U[i,1];}}
  "IDENTITY_RESIDUAL",Verify-1;
  for(i=1;i<=nrows(U);i++){{if(U[i,1]!=0){{"CORE",i;"MULT_BEGIN",i;print(string(U[i,1]));"MULT_END";}}}}
}}
quit;
'''

def model_fraction(value):
    return Fraction(value.numerator_as_long(),value.denominator_as_long())

def run_row(row):
    d,p,mask=row['d'],row['p'],row['representative_mask'];base=f'e08_d{d}_p{p}_m{mask}'
    solver,mu,ws,polys,lead,cached,mapping=build(row)
    result={k:row[k] for k in ('d','p','support_size','representative_mask','size')}
    result.update(cuts=[],status='not_started')
    rowstart=time.monotonic();per_row=30 if d<6 else 20
    result['base_smt_files']=write_small(HERE/(base+'_base.smt2'),solver.to_smt2())
    for iteration in range(50):
        if time.monotonic()>=DEADLINE or time.monotonic()-rowstart>=per_row:
            result['status']='budget_stop';break
        solver.set(timeout=min(30000,max(1,int(1000*(min(DEADLINE,rowstart+per_row)-time.monotonic())))))
        tick=time.monotonic();answer=solver.check()
        result['last_smt_seconds']=round(time.monotonic()-tick,6)
        if answer!=z3.sat:
            result['status']='covered_UNSAT' if answer==z3.unsat else 'SMT_unknown'
            if answer==z3.unknown:result['reason']=solver.reason_unknown()
            break
        model=solver.model();weights=[model_fraction(model.eval(w)) for w in ws]
        newrow=dict(row,weights=weights)
        gens,first,_=initial.initial_equations(newrow)
        stem=base+f'_c{iteration:02d}'
        check,out=singular(certificate_source(row,gens,first),stem)
        cut={'iteration':iteration,'weights':[str(w) for w in weights],'mu':str(model_fraction(model.eval(mu))),'singular':check,'source':stem+'.sing'}
        match=re.search(r'INIT_RESULT\s+(-?\d+)\s+(-?\d+)\s+(\d+)',out)
        if match:cut['initial_result']=list(map(int,match.groups()))
        if check['status']!='complete' or not re.search(r'IDENTITY_RESIDUAL\s+0(?:\s|$)',out):
            result['candidate']=cut
            result['status']='nonunit_candidate' if check['status']=='complete' and match else 'singular_incomplete'
            break
        multipliers=[(int(i),s.strip()) for i,s in re.findall(r'MULT_BEGIN\s+(\d+)\s*\n(.*?)\nMULT_END',out,re.S)]
        indices=[int(x)-1 for x in re.findall(r'CORE\s+(\d+)',out)]
        assert [i for i,_ in multipliers]==[i+1 for i in indices]
        replay=certificate_source(row,gens,first).split('ideal G=')[0]+'poly Verify=0;\n'
        replay+='\n'.join(f'Verify=Verify+({a})*I[{i}];' for i,a in multipliers)
        replay+='\n"REPLAY_RESIDUAL",Verify-1;\nquit;\n'
        replay_check,replay_out=singular(replay,stem+'_replay')
        cut['independent_replay']=replay_check
        if replay_check['status']!='complete' or not re.search(r'REPLAY_RESIDUAL\s+0(?:\s|$)',replay_out):
            result.update(status='certificate_replay_failed',candidate=cut);break
        original=sorted({mapping[i] for i in indices if i<len(mapping)})
        conditions=[];descriptions=[]
        for index in original:
            ts=cached[index];vals=[sum(weights[q] for q in mon)+v for mon,v in ts];low=min(vals)
            leaders=[j for j,v in enumerate(vals) if v==low]
            representative=leaders[0]
            mon,v=ts[representative];reference=z3.Sum([ws[q] for q in mon])+v
            for j,(mon,v) in enumerate(ts):
                value=z3.Sum([ws[q] for q in mon])+v
                conditions.append(value==reference if j in leaders else value>reference)
            descriptions.append({'polynomial_index_zero_based':index,'leader_term_indices_zero_based':leaders})
        cell=z3.And(*conditions) if conditions else z3.BoolVal(True)
        assert z3.is_true(model.eval(cell)), 'constructed cell must contain its witness'
        cut.update(unit_identity_checked=True,nonzero_lift_generator_indices_one_based=[i+1 for i in indices],original_polynomial_core_zero_based=original,cell=descriptions)
        # Replay-ready independent assertion, plus structured minimum-index sets.
        cut['cut_smt2']='(assert '+z3.Not(cell).sexpr()+')'
        solver.add(z3.Not(cell));result['cuts'].append(cut)
        write_small(HERE/(stem+'_cut.json'),json.dumps(cut,indent=2)+'\n')
        print(json.dumps({'d':d,'p':p,'mask':mask,'cut':iteration,'core':len(original),'singular_seconds':check['seconds']},sort_keys=True),flush=True)
    else:result['status']='cut_limit'
    result['seconds']=round(time.monotonic()-rowstart,6)
    result['final_smt_files']=write_small(HERE/(base+'_final.smt2'),solver.to_smt2())
    write_small(HERE/(base+'_summary.json'),json.dumps(result,indent=2)+'\n')
    return result

def main():
    rows=json.loads((HERE/'e04_weighted_screen.json').read_text())['results']
    rows=[r for r in rows if (r['d'],r['p']) in [(4,5),(5,3),(6,7)]]
    report={'seed':20261031,'z3_version':z3.get_version_string(),'scope':'necessary prevariety plus certified unit open-cell cuts; no tropical-basis assertion','results':[]}
    for row in rows:
        if time.monotonic()>=DEADLINE:break
        out=run_row(row)
        compact={k:v for k,v in out.items() if k!='cuts'}
        compact['cut_count']=len(out['cuts'])
        compact['cut_files']=[f'e08_d{out["d"]}_p{out["p"]}_m{out["representative_mask"]}_c{j:02d}_cut.json' for j in range(len(out['cuts']))]
        report['results'].append(compact)
        report['seconds']=round(time.monotonic()-START,6)
        write_small(HERE/'e08_tropical_cells.json',json.dumps(report,indent=2)+'\n')
        print(json.dumps({'SUPPORT_DONE':{k:out[k] for k in ('d','p','representative_mask','status','seconds')},'cuts':len(out['cuts'])},sort_keys=True),flush=True)
    print('TOTAL_SECONDS',round(time.monotonic()-START,6),flush=True)

if __name__=='__main__':main()
