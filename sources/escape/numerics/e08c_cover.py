#!/usr/bin/env python3.14
"""Final <=6-minute computation, compressed final SMT and sparse unit proofs.
No extra residue condition on positive-dimensional supports. Only one child.
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
from functools import lru_cache
import gzip,hashlib,importlib.util,json,os,re,subprocess,time
import z3
H=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('e08c_initial',H/'e05_initial_forms.py');M=importlib.util.module_from_spec(sp);sp.loader.exec_module(M)
z3.set_param('memory_max_size',2048);z3.set_param('smt.random_seed',20261031);z3.set_param('sat.random_seed',20261031)
START=time.monotonic();DEADLINE=START+300

def small_json(path,data):
    s=json.dumps(data,indent=2)+'\n';assert len(s.encode())<2**20;path.write_text(s)

def child(source,limit=10):
    p=subprocess.Popen(['Singular','--no-rc','--random=20261031','--cpus=1','--threads=1','--flint-threads=1','-q'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,cwd=H,env=dict(os.environ,OMP_NUM_THREADS='1',TMPDIR=str(H)))
    start=time.monotonic();first=True;peak=0;stop=None
    try:
        while True:
            try:out,_=p.communicate(source if first else None,timeout=.05);break
            except subprocess.TimeoutExpired:
                first=False
                try:peak=max(peak,M.resident(p.pid))
                except RuntimeError:pass
                if peak>=6*2**30:stop='memory_stop'
                elif time.monotonic()-start>=limit:stop='timeout'
                if stop:p.kill();out,_=p.communicate();break
    except BaseException:p.kill();p.communicate();raise
    status=stop or ('error' if p.returncode or re.search(r'^\s*\?',out,re.M) else 'complete')
    return {'status':status,'seconds':round(time.monotonic()-start,6),'sampled_peak_rss_bytes':peak},out

class Problem:
    def __init__(self,row):
        self.row=row;self.d=row['d'];self.p=row['p'];self.n=self.d**2
        d,p,n=self.d,self.p,self.n;S={q for q in range(1,n) if row['representative_mask']>>q&1};self.S=S
        def opp(q):r,k=divmod(q,d);return (-r%d)*d+(-k%d)
        self.opp=opp;neg={opp(q) for q in S};free=[q for q in range(1,n) if q not in S|neg and q<opp(q)]
        self.mu=z3.Real('mu');self.free={q:z3.Real(f'u{q}') for q in free};variables=[self.mu]+list(self.free.values());dim=len(variables)
        vecs=[]
        for q in range(n):
            v=[Fraction(0)]*(dim+1)
            if q==0:v[0]=Fraction(1,2);v[-1]=row['delta']-1
            elif q in S:pass
            elif q in neg:v[0]=1
            elif q==opp(q):v[0]=Fraction(1,2)
            elif q in self.free:v[1+free.index(q)]=1
            else:v[0]=1;v[1+free.index(opp(q))]=-1
            vecs.append(tuple(v))
        @lru_cache(None)
        def lin(v):return z3.Sum([z3.RealVal(str(c))*x for c,x in zip(v[:-1],variables) if c]+[z3.RealVal(str(v[-1]))])
        self.ws=[lin(v) for v in vecs];self.solver=z3.Solver();self.solver.set(timeout=30000);self.solver.add(self.mu>0)
        for x in self.free.values():self.solver.add(x>0,x<self.mu)
        polynomials,lead=M.initial_equations(row,return_polynomials=True);lead=lru_cache(None)(lead)
        self.cached=[];self.mapping=[];raw=0;formcount=0
        for index,poly in enumerate(polynomials):
            ts=[];counts=Counter()
            for mon,c in poly.items():
                info=lead(c)
                if not info:continue
                ts.append((mon,info[0],info[1]));v=[sum(vecs[q][i] for q in mon) for i in range(dim+1)];v[-1]+=info[0];counts[tuple(v)]+=1
            self.cached.append(ts)
            if ts:self.mapping.append(index)
            if not ts:continue
            low=z3.Real(f'lo{index}');values=[(lin(v),count) for v,count in counts.items()]
            self.solver.add(*[low<=v for v,count in values])
            repeated=[v==low for v,count in values if count>=2];single=[(v==low,1) for v,count in values if count==1]
            self.solver.add(z3.Or(*(repeated+([z3.PbGe(single,2)] if len(single)>=2 else []))))
            raw+=len(ts);formcount+=len(counts)
        baseline,self.first,_=M.initial_equations(row);self.extra=baseline[len(self.mapping):]
        self.minimal=len(S)==d and S==set(range(self.first//d*d,(self.first//d+1)*d))
        if self.minimal:
            _,L,root,_=M.rings(d,p);u=self.first//d
            for q in sorted(S):
                if q!=self.first:self.extra.append(f'z{q}-'+self.coeff(tuple(v%p for v in L.power(root,u*(q%d)))))
        self.header=f'ring R=({p},w),({",".join(["y","t"]+[f"z{q}" for q in range(n) if q!=self.first])}),dp;\nminpoly=w^2+1;\nshort=0;\n'
        self.group=[]
        for sign in (1,-1):
            for c in range(d):
                perm=[r*d+(sign*k+c*r)%d for r in range(d) for k in range(d)]
                if {perm[q] for q in S}==S:self.group.append((sign,c,perm))
        self.prior=[]
        prefixes=['e08']+(['e08b'] if self.minimal else [])
        for prefix in prefixes:
            for path in sorted(H.glob(f'{prefix}_d{d}_p{p}_m{row["representative_mask"]}_c??_cut.json')):
                cut=json.loads(path.read_text());self.add_orbit(cut['cell']);self.prior.append(path.name)
        self.stats={'free_pairs':len(free),'raw_terms':raw,'distinct_affine_forms_sum':formcount,'group_size':len(self.group),'fixed_minimal_residue_point':self.minimal,'prior_cut_files':self.prior}

    @staticmethod
    def coeff(c):return '('+('+'.join(str(v)+(f'*w^{i}' if i else '') for i,v in enumerate(c) if v) or '0')+')'
    def variable(self,q):return '1' if q==self.first else f'z{q}'
    def gens(self,weights):
        gens=[]
        for ts in self.cached:
            if not ts:continue
            low=min(v+sum(weights[q] for q in mon) for mon,v,c in ts)
            gens.append('+'.join(self.coeff(c)+'*'+'*'.join(self.variable(q) for q in mon) for mon,v,c in ts if v+sum(weights[q] for q in mon)==low))
        return gens+self.extra
    def cell(self,description,permutation=None):
        ws=self.ws if permutation is None else [self.ws[q] for q in permutation];conditions=[]
        for part in description:
            ts=self.cached[part['polynomial_index_zero_based']];leaders=part['leader_term_indices_zero_based'];mon,v,c=ts[leaders[0]];reference=z3.Sum([ws[q] for q in mon])+v
            for j,(mon,v,c) in enumerate(ts):
                value=z3.Sum([ws[q] for q in mon])+v;conditions.append(value==reference if j in leaders else value>reference)
        return z3.And(*conditions)
    def add_orbit(self,description):
        for sign,c,perm in self.group:self.solver.add(z3.Not(self.cell(description,perm)))
    def describe(self,indices,weights):
        description=[]
        for index in sorted({self.mapping[i] for i in indices if i<len(self.mapping)}):
            ts=self.cached[index];values=[v+sum(weights[q] for q in mon) for mon,v,c in ts];low=min(values)
            description.append({'polynomial_index_zero_based':index,'leader_term_indices_zero_based':[j for j,v in enumerate(values) if v==low]})
        return description

def unit(problem,gens):
    # Duplicate/scalar-proportional input generators need not burden lift.
    source=problem.header+'ideal I='+','.join(gens)+''';
ideal J; intvec origin; int nr=0; int i;int j;int dup;poly f;
for(i=1;i<=size(I);i++){if(I[i]!=0){f=I[i]/leadcoef(I[i]);dup=0;for(j=1;j<=nr;j++){if(f==J[j]/leadcoef(J[j])){dup=1;}}if(dup==0){nr++;J[nr]=I[i];origin[nr]=i;}}}
ideal G=slimgb(J);"INIT_RESULT",dim(G),vdim(G),size(G),nr;
if(size(G)==1 && G[1]==1){matrix U=lift(J,ideal(1));poly V=0;for(i=1;i<=nrows(U);i++){V=V+J[i]*U[i,1];} "IDENTITY_RESIDUAL",V-1;for(i=1;i<=nrows(U);i++){if(U[i,1]!=0){"MULT_BEGIN",origin[i];print(string(U[i,1]));"MULT_END";}}}
quit;
'''
    status,out=child(source);match=re.search(r'INIT_RESULT\s+(-?\d+)\s+(-?\d+)\s+(\d+)\s+(\d+)',out)
    if match:status['initial_result']=list(map(int,match.groups()))
    if status['status']!='complete' or not re.search(r'IDENTITY_RESIDUAL\s+0(?:\s|$)',out):return status,None,out[-3000:]
    members=[{'generator_index_zero_based':int(i)-1,'generator':gens[int(i)-1],'multiplier':s.strip()} for i,s in re.findall(r'MULT_BEGIN\s+(\d+)\s*\n(.*?)\nMULT_END',out,re.S)]
    replay=problem.header+'poly V=0;\n'+'\n'.join('V=V+('+m['multiplier']+')*('+m['generator']+');' for m in members)+'\n"REPLAY_RESIDUAL",V-1;quit;\n'
    proof,output=child(replay)
    if proof['status']!='complete' or not re.search(r'REPLAY_RESIDUAL\s+0(?:\s|$)',output):return dict(status,replay=proof),None,output[-3000:]
    status['independent_replay']=proof;return status,members,None

def save_smt(problem,stem):
    raw=problem.solver.to_smt2().encode();compressed=gzip.compress(raw,mtime=0);files=[]
    for i in range(0,len(compressed),900000):
        name=stem+f'_final.smt2.gz.part{i//900000:03d}';(H/name).write_bytes(compressed[i:i+900000]);files.append(name)
    return {'files':files,'uncompressed_bytes':len(raw),'compressed_bytes':len(compressed),'uncompressed_sha256':hashlib.sha256(raw).hexdigest()}

def run(row,seconds):
    started=time.monotonic();end=min(DEADLINE,started+seconds);mask=row['representative_mask'];stem=f'e08c_d6_p7_m{mask}';problem=Problem(row)
    result={k:row[k] for k in ('d','p','support_size','representative_mask','size')};result.update(stats=problem.stats,new_cut_files=[],status='budget_stop')
    for iteration in range(200):
        if time.monotonic()>=end:break
        problem.solver.set(timeout=min(30000,max(1,int(1000*(end-time.monotonic())))))
        t=time.monotonic();answer=problem.solver.check();smt_time=time.monotonic()-t
        if answer!=z3.sat:
            result['status']='covered_UNSAT' if answer==z3.unsat else 'SMT_unknown'
            if answer==z3.unknown:result['reason']=problem.solver.reason_unknown()
            break
        model=problem.solver.model();weights=[Fraction(model.eval(x).numerator_as_long(),model.eval(x).denominator_as_long()) for x in problem.ws]
        gens=problem.gens(weights);status,members,error=unit(problem,gens)
        if members is None:
            result.update(status='uncertified_initial',candidate={'weights':[str(w) for w in weights],'mu':str(model.eval(problem.mu)),'singular':status,'output_tail':error});break
        indices=[m['generator_index_zero_based'] for m in members];description=problem.describe(indices,weights)
        assert z3.is_true(model.eval(problem.cell(description)))
        cut={'schema':'e08c-sparse-unit-v1','d':row['d'],'p':row['p'],'mask':mask,'weights':[str(w) for w in weights],'mu':str(model.eval(problem.mu)),'first_label':problem.first,'fixed_minimal_residue_point':problem.minimal,'generator_count':len(gens),'members':members,'cell':description,'group_images':[(s,c) for s,c,p in problem.group],'singular':status,'smt_seconds':round(smt_time,6)}
        name=stem+f'_c{iteration:03d}.json';small_json(H/name,cut);result['new_cut_files'].append(name);problem.add_orbit(description)
        print(json.dumps({'mask':mask,'cut':iteration,'core':len(description),'lift_seconds':status['seconds'],'smt_seconds':round(smt_time,4),'elapsed':round(time.monotonic()-started,2)}),flush=True)
    else:result['status']='cut_limit'
    result['seconds']=round(time.monotonic()-started,6);result['final_smt']=save_smt(problem,stem);small_json(H/(stem+'_summary.json'),result);return result

def main():
    rows=json.loads((H/'e04_weighted_screen.json').read_text())['results'];results=[]
    for mask,seconds in [(352325568,45),(704647104,45),(4032,65),(258048,65),(1056968640,35)]:
        if time.monotonic()>=DEADLINE:break
        row=next(r for r in rows if r['d']==6 and r['p']==7 and r['representative_mask']==mask)
        result=run(row,seconds);results.append(result);small_json(H/'e08c_cover_summary.json',{'seed':20261031,'results':results,'seconds':round(time.monotonic()-START,6)})
        print(json.dumps({'SUPPORT_DONE':mask,'status':result['status'],'new_cuts':len(result['new_cut_files']),'seconds':result['seconds']}),flush=True)
    print('TOTAL_SECONDS',round(time.monotonic()-START,6),flush=True)
if __name__=='__main__':main()
