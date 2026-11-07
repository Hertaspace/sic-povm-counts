#!/usr/bin/env python3.14
"""p=7 exact initial-cell work. One monitored child, no old-tree writes.

All arithmetic is exact in GF(49) or Q, seed 20261031.  Only own e10_*
artifacts are written.  Children are killed only by their exact recorded PID.
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
sys.dont_write_bytecode = True
from pathlib import Path
from fractions import Fraction
from functools import lru_cache
import gzip, hashlib, importlib.util, json, os, random, re, subprocess, time
import z3

H = Path(__file__).resolve().parent
OLD = public_root(__file__) / 'sources/escape/numerics'
sp = importlib.util.spec_from_file_location('p7_old_c', OLD/'e08c_cover.py')
C = importlib.util.module_from_spec(sp)
sp.loader.exec_module(C)
C.H = H
SEED = 20261031
START = time.monotonic()
ROWS = json.loads((OLD/'e04_weighted_screen.json').read_text())['results']
z3.set_param('memory_max_size', 10000)

def small_json(name, obj):
    raw = (json.dumps(obj, indent=2)+'\n').encode()
    assert len(raw)<2**20, (name, len(raw))
    (H/name).write_bytes(raw)

def packed(name, raw):
    if isinstance(raw, str): raw=raw.encode()
    data=gzip.compress(raw, mtime=0); files=[]
    for i in range(0,len(data),900000):
        f=name+f'.gz.part{i//900000:03d}'
        (H/f).write_bytes(data[i:i+900000]);files.append(f)
    return dict(files=files,uncompressed_bytes=len(raw),compressed_bytes=len(data),
                uncompressed_sha256=hashlib.sha256(raw).hexdigest())

def child(source, limit=30, kind='Singular'):
    command=(['Singular','--no-rc',f'--random={SEED}','--cpus=1','--threads=1','--flint-threads=1','-q']
             if kind=='Singular' else ['z3','memory_max_size=10000','-in'])
    p=subprocess.Popen(command,stdin=subprocess.PIPE,stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT,text=True,cwd=H,
                       env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',OMP_NUM_THREADS='1',TMPDIR=str(H)))
    start=time.monotonic(); first=True; peak=0; stop=None;last_report=start
    small_json('e10_p7_live_child.json',dict(pid=p.pid,kind=kind,status='running',limit_seconds=limit,
                                           source_sha256=hashlib.sha256(source.encode()).hexdigest()))
    try:
        while True:
            try:out,_=p.communicate(source if first else None,timeout=.05);break
            except subprocess.TimeoutExpired as partial:
                first=False
                try:peak=max(peak,C.M.resident(p.pid))
                except RuntimeError:pass
                if peak>=16*2**30:stop='memory_stop'
                elif time.monotonic()-start>=limit:stop='timeout'
                if time.monotonic()-last_report>=1:
                    small_json('e10_p7_live_child.json',dict(pid=p.pid,kind=kind,status='running',limit_seconds=limit,
                               seconds=round(time.monotonic()-start,6),sampled_peak_rss_bytes=peak,
                               output_tail=(partial.output or b'')[-2000:].decode(errors='replace') if isinstance(partial.output,bytes) else (partial.output or '')[-2000:]))
                    last_report=time.monotonic()
                if stop:p.kill();out,_=p.communicate();break
    except BaseException:
        p.kill();p.communicate()
        small_json('e10_p7_live_child.json',dict(pid=p.pid,kind=kind,status='interrupted',returncode=p.returncode,
                   seconds=round(time.monotonic()-start,6),sampled_peak_rss_bytes=peak))
        raise
    status=stop or ('error' if p.returncode or re.search(r'^\s*\?',out,re.M) else 'complete')
    result=dict(status=status,pid=p.pid,returncode=p.returncode,seconds=round(time.monotonic()-start,6),
                sampled_peak_rss_bytes=peak,command=command)
    small_json('e10_p7_live_child.json',result)
    return result,out

COMPONENT_RELATIONS=['z8-5','z10-4','z9-5*z7','z11-4*z7',
                     'z26-2*z24','z28-4*z24','z27-2*z25','z29-4*z25']

def problem(mask, prior=True, component=False):
    row=next(r for r in ROWS if r['d']==6 and r['p']==7 and r['representative_mask']==mask)
    # C.Problem reads only old immutable cut JSON; all writers use new H.
    C.H=OLD
    try:p=C.Problem(row)
    finally:C.H=H
    if prior:
        for file in sorted(OLD.glob(f'e08c_d6_p7_m{mask}_*c[0-9][0-9][0-9].json')):
            p.add_orbit(json.loads(file.read_text())['cell'])
    p.residue_component_normalization=None
    if component:
        assert mask==1056968640
        p.extra.extend(COMPONENT_RELATIONS)
        p.residue_component_normalization=dict(a_support=[0,3],b_support=[2,5],
                relations=COMPONENT_RELATIONS,action='Weyl X translation to residue class a=0 mod 3')
    return p

def dedup(p, gens):
    source=p.header+'ideal I='+','.join(gens)+''';
ideal J; intvec origin; int nr=0; int i;int j;int dup;poly f;
for(i=1;i<=size(I);i++){if(I[i]!=0){f=I[i]/leadcoef(I[i]);dup=0;for(j=1;j<=nr;j++){if(f==J[j]/leadcoef(J[j])){dup=1;}}if(dup==0){nr++;J[nr]=I[i];origin[nr]=i;}}}
for(i=1;i<=nr;i++){"DEDUP",origin[i];}quit;
'''
    st,out=child(source,10); assert st['status']=='complete', (st,out[-2000:])
    return [int(i)-1 for i in re.findall(r'DEDUP\s+(\d+)',out)]

def is_unit(p,gens,indices,limit):
    source=p.header+'ideal J='+','.join(gens[i] for i in indices)+''';
ideal G=slimgb(J);"INIT_RESULT",dim(G),vdim(G),size(G);quit;
'''
    st,out=child(source,limit)
    m=re.search(r'INIT_RESULT\s+(-?\d+)\s+(-?\d+)\s+(\d+)',out)
    if m:st['initial_result']=list(map(int,m.groups()))
    return st, (st['status']=='complete' and st.get('initial_result')==[-1,0,1]), out

def identity(p,gens,indices,limit,algorithm='std'):
    source=p.header+'ideal J='+','.join(gens[i] for i in indices)+''';
matrix UU; matrix U=lift(J,ideal(1),UU,"'''+algorithm+'''");poly V=0;int i;
for(i=1;i<=nrows(U);i++){V=V+J[i]*U[i,1];}
"IDENTITY_RESIDUAL",V-1;
for(i=1;i<=nrows(U);i++){if(U[i,1]!=0){"MULT_BEGIN",i;print(string(U[i,1]));"MULT_END";}}
quit;
'''
    st,out=child(source,limit)
    if st['status']!='complete' or not re.search(r'IDENTITY_RESIDUAL\s+0(?:\s|$)',out):return st,None,out
    members=[dict(generator_index_zero_based=indices[int(i)-1],generator=gens[indices[int(i)-1]],multiplier=s.strip())
             for i,s in re.findall(r'MULT_BEGIN\s+(\d+)\s*\n(.*?)\nMULT_END',out,re.S)]
    replay=p.header+'poly V=0;\n'+'\n'.join('V=V+('+m['multiplier']+')*('+m['generator']+');' for m in members)+'\n"REPLAY_RESIDUAL",V-1;quit;\n'
    replay_st,replay_out=child(replay,30)
    assert replay_st['status']=='complete' and 'REPLAY_RESIDUAL 0' in replay_out,(replay_st,replay_out[-1000:])
    st['independent_replay']=replay_st
    return st,members,out

def certify(p, weights, indices, name, limit=60, algorithm='slimgb'):
    gens=p.gens(weights);st,members,out=identity(p,gens,indices,limit,algorithm)
    result=dict(status='uncertified_initial',singular=st,weights=list(map(str,weights)))
    if members is None:
        result['output_tail']=out[-2000:];return result
    desc=p.describe([m['generator_index_zero_based'] for m in members],weights)
    cut=dict(schema='e10-sparse-unit-v1',d=6,p=7,mask=p.row['representative_mask'],weights=list(map(str,weights)),
             first_label=p.first,fixed_minimal_residue_point=p.minimal,members=members,cell=desc,
             group_images=[(s,c) for s,c,perm in p.group],singular=st)
    if p.residue_component_normalization:cut['residue_component_normalization']=p.residue_component_normalization
    raw=json.dumps(cut,indent=2)+'\n'
    manifest=packed(name+'.json',raw)
    result.update(status='certified',certificate=manifest,nonzero_members=len(members),cell=desc)
    p.add_orbit(desc)
    return result

def slim():
    mask=1056968640;p=problem(mask)
    weights=[Fraction(x) for x in json.loads((OLD/f'e08c_d6_p7_m{mask}_summary.json').read_text())['candidate']['weights']]
    gens=p.gens(weights);indices=dedup(p,gens)
    begin=time.monotonic()
    output=dict(seed=SEED,mask=mask,algorithm='Singular lift fourth argument slimgb',
                certificate_result=certify(p,weights,indices,'e10_p7_two_slim_c000',600))
    if output['certificate_result']['status']=='certified':
        p.solver.set(timeout=60000);answer=p.solver.check();output['remaining_smt_status']=str(answer)
        output['final_smt']=packed('e10_p7_two_slim_final.smt2',p.solver.to_smt2())
        if answer==z3.sat:
            m=p.solver.model();output['remaining_weights']=[str(Fraction(m.eval(x).numerator_as_long(),m.eval(x).denominator_as_long())) for x in p.ws]
    output['seconds']=round(time.monotonic()-begin,6)
    small_json('e10_p7_slim.json',output)
    print(json.dumps(output,indent=2),flush=True)

def tpower():
    mask=1056968640;p=problem(mask);begin=time.monotonic()
    weights=[Fraction(x) for x in json.loads((OLD/f'e08c_d6_p7_m{mask}_summary.json').read_text())['candidate']['weights']]
    gens=p.gens(weights);indices=dedup(p,gens)
    inv=gens.index('t*y-1');indices=[i for i in indices if i!=inv]
    source=p.header+'ideal J='+','.join(gens[i] for i in indices)+''';
ideal G=slimgb(J);"UNSATURATED_RESULT",dim(G),vdim(G),size(G);
int k; poly f=t; for(k=1;k<=32;k++){if(reduce(f,G)==0){"TPOWER",k;break;} f=f*t;}
quit;
'''
    st,out=child(source,120);print(json.dumps(st),out,flush=True)
    output=dict(seed=SEED,mask=mask,weights=list(map(str,weights)),unsaturated_gb=st,unsaturated_output=out[-3000:])
    power=re.search(r'TPOWER\s+(\d+)',out)
    if st['status']=='complete' and power:
        k=int(power[1]);output['t_power']=k
        source=p.header+'ideal J='+','.join(gens[i] for i in indices)+''';
matrix UU; matrix U=lift(J,ideal(t^'''+str(k)+'''),UU,"slimgb");poly V=0;int i;
for(i=1;i<=nrows(U);i++){V=V+J[i]*U[i,1];}
"TPOWER_RESIDUAL",V-t^'''+str(k)+''';
for(i=1;i<=nrows(U);i++){if(U[i,1]!=0){"MULT_BEGIN",i;print(string(U[i,1]));"MULT_END";}}
quit;
'''
        lift_st,lift_out=child(source,600);output['lift']=lift_st
        if lift_st['status']=='complete' and re.search(r'TPOWER_RESIDUAL\s+0(?:\s|$)',lift_out):
            members=[dict(generator_index_zero_based=indices[int(i)-1],generator=gens[indices[int(i)-1]],
                          multiplier=f'y^{k}*('+s.strip()+')')
                     for i,s in re.findall(r'MULT_BEGIN\s+(\d+)\s*\n(.*?)\nMULT_END',lift_out,re.S)]
            members.append(dict(generator_index_zero_based=inv,generator=gens[inv],
                                multiplier='-('+ '+'.join(f'(t*y)^{j}' for j in range(k))+')'))
            replay=p.header+'poly V=0;\n'+'\n'.join('V=V+('+m['multiplier']+')*('+m['generator']+');' for m in members)+'\n"REPLAY_RESIDUAL",V-1;quit;\n'
            rs,ro=child(replay,60);assert rs['status']=='complete' and 'REPLAY_RESIDUAL 0' in ro,(rs,ro[-1000:])
            desc=p.describe([m['generator_index_zero_based'] for m in members],weights)
            cut=dict(schema='e10-sparse-unit-v1',d=6,p=7,mask=mask,weights=list(map(str,weights)),first_label=p.first,
                     fixed_minimal_residue_point=False,members=members,cell=desc,group_images=[(s,c) for s,c,perm in p.group],
                     singular=lift_st,independent_replay=rs,construction=f't^{k} nilpotence followed by inverse identity')
            output['certificate']=packed('e10_p7_two_tpower_c000.json',json.dumps(cut,indent=2)+'\n')
            p.add_orbit(desc);p.solver.set(timeout=60000);output['remaining_smt_status']=str(p.solver.check())
            output['final_smt']=packed('e10_p7_two_tpower_final.smt2',p.solver.to_smt2())
            if output['remaining_smt_status']=='sat':
                m=p.solver.model();output['remaining_weights']=[str(Fraction(m.eval(x).numerator_as_long(),m.eval(x).denominator_as_long())) for x in p.ws]
        else:output['lift_output_tail']=lift_out[-3000:]
    output['seconds']=round(time.monotonic()-begin,6)
    small_json('e10_p7_tpower.json',output);print(json.dumps(output,indent=2),flush=True)

def normalized(component=False,linear=False):
    # The initial ideal has a second torus grading fixing all S coordinates.
    # Normalize t=1, then homogenize the extracted identity in h with h^2=t.
    # Even projection produces a genuine original t^k membership identity;
    # the final saved certificate does NOT depend on the normalization lemma.
    sys.path.insert(0,str(OLD))
    from e90_support_audit import finite_algebra
    from e90_initial_audit import Polynomial,parse_polynomial
    mask=1056968640;p=problem(mask,component=component);begin=time.monotonic()
    weights=[Fraction(x) for x in json.loads((OLD/f'e08c_d6_p7_m{mask}_summary.json').read_text())['candidate']['weights']]
    gens=p.gens(weights);F,_=finite_algebra(6,7);S=p.S;neg={p.opp(q) for q in S}
    grades={f'z{q}':0 if q in S else 2 if q in neg else 1 for q in range(36)}
    grades.update(t=2,y=-2)
    polys=[parse_polynomial(g,F,36) for g in gens];degrees=[];normalized_polys=[]
    for poly in polys:
        ds={sum(grades[x] for x in mon) for mon in poly.terms};assert len(ds)<=1,ds
        degrees.append(next(iter(ds),0));np=Polynomial(F)
        for mon,c in poly.terms.items():
            np=np+Polynomial(F,{tuple(x for x in mon if x not in ('t','y')):c})
        normalized_polys.append(np)
    def txt(poly):
        return '+'.join(F.text(c)+('' if not mon else '*'+'*'.join(mon)) for mon,c in sorted(poly.terms.items())) or '0'
    working=normalized_polys
    basis={}
    def scalar(c):return Polynomial(F,{():c}) if c!=F.zero else Polynomial(F)
    if linear:
        # RREF of actual affine-linear normalized inputs, with constant
        # source combinations. No unproved equation is inserted here.
        for i,np in enumerate(normalized_polys):
            if not np.terms or any(len(mon)>1 for mon in np.terms):continue
            f=np;rep={i:F.one}
            for v,(ell,src) in basis.items():
                c=f.terms.get((v,),F.zero)
                if c!=F.zero:
                    f=f-scalar(c)*ell
                    for j,a in src.items():
                        rep[j]=F.sub(rep.get(j,F.zero),F.mul(c,a))
                        if rep[j]==F.zero:rep.pop(j)
            if not f.terms:continue
            vs=[mon[0] for mon in f.terms if mon]
            assert vs,'affine input equations already contain a constant contradiction'
            v=min(vs);inv=F.inverse(f.terms[(v,)])
            f=scalar(inv)*f;rep={j:F.mul(inv,a) for j,a in rep.items()}
            for u,(ell,src) in list(basis.items()):
                c=ell.terms.get((v,),F.zero)
                if c!=F.zero:
                    ell=ell-scalar(c)*f;src=dict(src)
                    for j,a in rep.items():
                        src[j]=F.sub(src.get(j,F.zero),F.mul(c,a))
                        if src[j]==F.zero:src.pop(j)
                    basis[u]=(ell,src)
            basis[v]=(f,rep)
        substitutions={v:parse_polynomial(v,F,36)-ell for v,(ell,src) in basis.items()}
        def substitute(poly):
            result=Polynomial(F)
            for mon,c in poly.terms.items():
                term=scalar(c)
                for v in mon:term=term*substitutions.get(v,parse_polynomial(v,F,36))
                result=result+term
            return result
        working=[substitute(f) for f in normalized_polys]
    kept=[];seen=set()
    for i,np in enumerate(working):
        if not np.terms:continue
        inv=F.inverse(np.terms[min(np.terms)])
        key=tuple(sorted((m,F.mul(c,inv)) for m,c in np.terms.items()))
        if key not in seen:kept.append(i);seen.add(key)
    kept.sort(key=lambda i:(max(map(len,working[i].terms)),len(working[i].terms),i))
    output=dict(seed=SEED,mask=mask,weights=list(map(str,weights)),grading=grades,
                original_count=len(gens),normalized_dedup_count=len(kept),homogeneous_degrees=degrees,
                normalized_indices=kept)
    namespace='e10_p7_linear' if linear else 'e10_p7_component' if component else 'e10_p7_normalized'
    if linear:output['linear_elimination']=dict(pivots=sorted(basis),relations={v:txt(ell) for v,(ell,src) in basis.items()},
                   source_combinations={v:{str(j):F.text(c) for j,c in src.items()} for v,(ell,src) in basis.items()})
    if component:
        # Literal reconstruction independently checks the eight linear
        # component equations without specializing any of its parameters.
        _,tau=finite_algebra(6,7)
        zs=[Polynomial(F) for _ in range(36)]
        for q in p.S:zs[q]=parse_polynomial(p.variable(q),F,36)
        replacements={8:'5',10:'4',9:'5*z7',11:'4*z7',26:'2*z24',28:'4*z24',27:'2*z25',29:'4*z25'}
        for q,s in replacements.items():zs[q]=parse_polynomial(s,F,36)
        entries={}
        for i in range(6):
            for j in range(6):
                u=(i-j)%6;value=Polynomial(F)
                for v in range(6):value=value+zs[6*u+v]*Polynomial(F,{():F.power(tau,(u*v+2*v*j)%12)})
                if value.terms:entries[(i,j)]=value
        assert set(entries)=={(0,2),(0,5),(3,2),(3,5)},set(entries)
        determinant=entries[0,5]*entries[3,2]-entries[0,2]*entries[3,5]
        conic=parse_polynomial('3*z7^2+z24^2+3*z25^2-1',F,36)
        pivot=min(conic.terms);scalar=F.mul(determinant.terms[pivot],F.inverse(conic.terms[pivot]))
        assert determinant==conic*Polynomial(F,{():scalar})
        output['component_validation']=dict(matrix_entries={str(k):txt(v) for k,v in entries.items()},
                    determinant=txt(determinant),conic_scalar=F.text(scalar),parameters=['z7','z24','z25'],
                    projective_dimension=2,all_forbidden_matrix_entries='identically zero')
        small_json('e10_p7_component_validation.json',output['component_validation'])
    small_json(namespace+'_progress.json',output)
    source=p.header+'ideal J='+','.join(txt(working[i]) for i in kept)+''';
ideal G=slimgb(J);"INIT_RESULT",dim(G),vdim(G),size(G);
matrix UU; matrix U=lift(J,ideal(1),UU,"slimgb");poly V=0;int i;
for(i=1;i<=nrows(U);i++){V=V+J[i]*U[i,1];}
"NORMALIZED_RESIDUAL",V-1;
for(i=1;i<=nrows(U);i++){if(U[i,1]!=0){"MULT_BEGIN",i;print(string(U[i,1]));"MULT_END";}}
quit;
'''
    st,out=child(source,600);output['normalized_lift']=st;output['normalized_output_tail']=out[-3000:]
    if st['status']=='complete' and re.search(r'NORMALIZED_RESIDUAL\s+0(?:\s|$)',out):
        ai=[(kept[int(i)-1],parse_polynomial(s.strip(),F,36))
            for i,s in re.findall(r'MULT_BEGIN\s+(\d+)\s*\n(.*?)\nMULT_END',out,re.S)]
        if linear:
            assert all(v not in mon for v in basis for i,a in ai for mon in a.terms)
            restored={}
            for i,a in ai:
                restored[i]=restored.get(i,Polynomial(F))+a
                diff=normalized_polys[i]-working[i];qs={v:Polynomial(F) for v in basis}
                while diff.terms:
                    eligible=[(mon,c) for mon,c in diff.terms.items() if any(v in mon for v in basis)]
                    assert eligible,'linear division must have zero remainder'
                    mon,c=eligible[0];v=next(v for v in basis if v in mon);reduced=list(mon);reduced.remove(v)
                    q=Polynomial(F,{tuple(reduced):c});ell,src=basis[v]
                    qs[v]=qs[v]+q;diff=diff-q*ell
                for v,q in qs.items():
                    if not q.terms:continue
                    for j,c in basis[v][1].items():
                        restored[j]=restored.get(j,Polynomial(F))-a*q*scalar(c)
            ai=[(i,a) for i,a in sorted(restored.items()) if a.terms]
            check=Polynomial(F)
            for i,a in ai:check=check+a*normalized_polys[i]
            assert check==1,'linear elimination restoration must give normalized identity 1'
            output['linear_restoration_identity']='exactly 1 over GF49'
        assert all('t' not in mon and 'y' not in mon for i,a in ai for mon in a.terms)
        N=max(degrees[i]+sum(grades[x] for x in mon) for i,a in ai for mon in a.terms)
        N+=N%2;k=N//2; assert k>=1
        members=[]
        for i,a in ai:
            b=Polynomial(F)
            for mon,c in a.terms.items():
                h=N-degrees[i]-sum(grades[x] for x in mon);assert h>=0
                if h%2==0:b=b+Polynomial(F,{tuple(sorted(mon+('t',)*(h//2))):c})
            if b.terms:members.append(dict(generator_index_zero_based=i,generator=gens[i],multiplier=f'y^{k}*('+txt(b)+')'))
        inv=gens.index('t*y-1')
        members.append(dict(generator_index_zero_based=inv,generator=gens[inv],
                            multiplier='-('+ '+'.join(f'(t*y)^{j}' for j in range(k))+')'))
        # Independent Python arithmetic checks the original ideal identity.
        total=Polynomial(F)
        for m in members:total=total+parse_polynomial(m['multiplier'],F,36)*polys[m['generator_index_zero_based']]
        assert total==1,'homogenized original identity must equal 1'
        replay=p.header+'poly V=0;\n'+'\n'.join('V=V+('+m['multiplier']+')*('+m['generator']+');' for m in members)+'\n"REPLAY_RESIDUAL",V-1;quit;\n'
        rs,ro=child(replay,60);assert rs['status']=='complete' and 'REPLAY_RESIDUAL 0' in ro,(rs,ro[-1000:])
        desc=p.describe([m['generator_index_zero_based'] for m in members],weights)
        cut=dict(schema='e10-sparse-unit-v1',d=6,p=7,mask=mask,weights=list(map(str,weights)),first_label=p.first,
                 fixed_minimal_residue_point=False,members=members,cell=desc,group_images=[(s,c) for s,c,perm in p.group],
                 singular=st,independent_replay=rs,independent_python_identity='exactly 1',
                 construction=dict(method='t=1 normalization, h^2=t homogenization, even projection',homogenizing_degree=N,t_power=k))
        if p.residue_component_normalization:cut['residue_component_normalization']=p.residue_component_normalization
        output['certificate']=packed(namespace+'_c000.json',json.dumps(cut,indent=2)+'\n')
        output['nonzero_members']=len(members);output['original_python_identity']='exactly 1'
        p.add_orbit(desc);p.solver.set(timeout=60000);output['remaining_smt_status']=str(p.solver.check())
        output['final_smt']=packed(namespace+'_final.smt2',p.solver.to_smt2())
        if output['remaining_smt_status']=='sat':
            m=p.solver.model();ws=[Fraction(m.eval(x).numerator_as_long(),m.eval(x).denominator_as_long()) for x in p.ws]
            output['remaining_weights']=list(map(str,ws));output['remaining_candidate']=candidate(p,ws,'e10_p7_two_remaining_candidate')
    output['seconds']=round(time.monotonic()-begin,6)
    small_json(namespace+'.json',output);print(json.dumps(output,indent=2),flush=True)

def candidate(p, weights, name):
    desc=p.describe(list(range(len(p.mapping))),weights)
    data=dict(schema='e10-exact-initial-candidate-v1',d=6,p=7,mask=p.row['representative_mask'],
              weights=list(map(str,weights)),first_label=p.first,
              fixed_minimal_residue_point=p.minimal,generators=p.gens(weights),
              all_original_leaders=desc,
              generator_source_sha256=hashlib.sha256((OLD/'e05_initial_forms.py').read_bytes()).hexdigest(),
              status='Necessary tropical candidate only; no residue point or lift is asserted')
    return packed(name+'.json',json.dumps(data,indent=2)+'\n')

def r1():
    mask=4032;p=problem(mask);begin=time.monotonic();end=begin+600
    seed=None
    if (H/'e31_residue_prior.json').exists():
        old=json.loads((H/'e31_residue_prior.json').read_text());manifest=old['smt'];source_root=H
        seed=[Fraction(x) for x in old['weights']]
    else:
        old=next(r for r in json.loads((OLD/'e08c_seed_minimal.json').read_text())['results'] if r['mask']==mask)
        manifest=old['final_smt'];source_root=OLD
    raw=gzip.decompress(b''.join((source_root/f).read_bytes() for f in manifest['files']))
    assert hashlib.sha256(raw).hexdigest()==manifest['uncompressed_sha256']
    p.solver=z3.Solver();p.solver.from_string(raw.decode())
    output=dict(seed=SEED,mask=mask,prior_final_smt=manifest,prior_smt_root=str(source_root),certificates=[],status='running',
                versions=dict(python=sys.version,z3=z3.get_version_string()))
    for i in range(1000):
        if time.monotonic()>=end:output['status']='batch_time_reached';break
        p.solver.set(timeout=min(60000,max(1,int(1000*(end-time.monotonic())))))
        tick=time.monotonic();answer=z3.sat if i==0 and seed is not None else p.solver.check();smt=time.monotonic()-tick
        if answer!=z3.sat:
            output['status']='covered_UNSAT' if answer==z3.unsat else 'SMT_unknown'
            if answer==z3.unknown:output['reason']=p.solver.reason_unknown()
            break
        if i==0 and seed is not None:weights=seed
        else:
            m=p.solver.model();weights=[Fraction(m.eval(x).numerator_as_long(),m.eval(x).denominator_as_long()) for x in p.ws]
        if i==0:
            output['first_remaining_weights']=list(map(str,weights))
            output['first_candidate']=candidate(p,weights,'e10_p7_r1_first_candidate')
            small_json('e10_p7_r1_progress.json',output)
            print('FIRST_R1_WEIGHTS',json.dumps(list(map(str,weights))),flush=True)
        gens=p.gens(weights);indices=dedup(p,gens)
        result=certify(p,weights,indices,f'e10_p7_r1_c{i:04d}',30,algorithm='std')
        if result['status']!='certified':
            st,unit,out=is_unit(p,gens,indices,30)
            output.update(status='uncertified_initial',failed_identity=result,initial_check=st,
                          remaining_candidate=candidate(p,weights,'e10_p7_r1_remaining_candidate'))
            break
        output['certificates'].append(result['certificate'])
        output['seconds']=round(time.monotonic()-begin,6)
        small_json('e10_p7_r1_progress.json',output)
        print(json.dumps(dict(mask=mask,cut=i,core=len(result['cell']),identity_seconds=result['singular']['seconds'],
                              smt_seconds=round(smt,6),elapsed=output['seconds'])),flush=True)
    else:output['status']='batch_cut_limit'
    output['final_smt']=packed('e10_p7_r1_final.smt2',p.solver.to_smt2())
    output['seconds']=round(time.monotonic()-begin,6)
    if output['status']!='covered_UNSAT':
        p.solver.set(timeout=60000);tick=time.monotonic();answer=p.solver.check()
        output['closing_check']=dict(answer=str(answer),seconds=round(time.monotonic()-tick,6))
        if answer==z3.unsat:output['status']='covered_UNSAT'
        elif answer==z3.sat:
            m=p.solver.model();weights=[Fraction(m.eval(x).numerator_as_long(),m.eval(x).denominator_as_long()) for x in p.ws]
            output['remaining_weights']=list(map(str,weights))
            output['remaining_candidate']=candidate(p,weights,'e10_p7_r1_remaining_candidate')
    small_json('e10_p7_r1.json',output)
    print(json.dumps({k:v for k,v in output.items() if k!='certificates'},indent=2),flush=True)

def r1_plain():
    # Diagnostic requested by coordinator: remove every e31 strengthening.
    p=problem(4032);begin=time.monotonic()
    prior=json.loads((OLD/'e08c_r1_cli.json').read_text())['source_manifest']
    raw=gzip.decompress(b''.join((OLD/f).read_bytes() for f in prior['files']))
    assert hashlib.sha256(raw).hexdigest()==prior['uncompressed_sha256']
    p.solver=z3.Solver();p.solver.from_string(raw.decode())
    certificates=json.loads((H/'e10_p7_r1.json').read_text())['certificates']
    for manifest in certificates:
        raw=gzip.decompress(b''.join((H/f).read_bytes() for f in manifest['files']))
        assert hashlib.sha256(raw).hexdigest()==manifest['uncompressed_sha256']
        cut=json.loads(raw);p.add_orbit(cut['cell'])
    p.solver.set(timeout=60000);tick=time.monotonic();answer=p.solver.check()
    output=dict(seed=SEED,mask=4032,prior_final_smt=prior,certificates=certificates,
                status='covered_UNSAT' if answer==z3.unsat else str(answer),
                new_source_cells=len(certificates),uses_e31_strengthening=False,
                check_seconds=round(time.monotonic()-tick,6),seconds=round(time.monotonic()-begin,6),
                final_smt=packed('e10_p7_r1_plain_final.smt2',p.solver.to_smt2()))
    if answer==z3.unknown:output['reason']=p.solver.reason_unknown()
    if answer==z3.sat:
        m=p.solver.model();weights=[Fraction(m.eval(x).numerator_as_long(),m.eval(x).denominator_as_long()) for x in p.ws]
        output['remaining_weights']=list(map(str,weights))
        output['remaining_candidate']=candidate(p,weights,'e10_p7_r1_plain_remaining_candidate')
    small_json('e10_p7_r1_plain.json',output);print(json.dumps(output,indent=2),flush=True)

def core():
    mask=1056968640;p=problem(mask)
    weights=[Fraction(x) for x in json.loads((OLD/f'e08c_d6_p7_m{mask}_summary.json').read_text())['candidate']['weights']]
    gens=p.gens(weights);active=dedup(p,gens);begin=time.monotonic();deadline=begin+600
    history=[];output=dict(seed=SEED,mask=mask,weights=list(map(str,weights)),original_count=len(gens),dedup_count=len(active),history=history)
    rng=random.Random(SEED)
    # Deterministic chunk deletion. Small remaining cores can avoid the very
    # expensive source module used by lift with all 281 inputs.
    order=active[:];rng.shuffle(order)
    for block in (64,32,16,8,4,2,1):
        for offset in range(0,len(order),block):
            if time.monotonic()>=deadline:break
            remove=set(order[offset:offset+block]);candidate=[i for i in active if i not in remove]
            if len(candidate)==len(active) or not candidate:continue
            st,unit,out=is_unit(p,gens,candidate,min(12,max(1,deadline-time.monotonic())))
            item=dict(block=block,offset=offset,before=len(active),candidate=len(candidate),unit=unit,child=st)
            if unit:active=candidate
            item['after']=len(active);history.append(item)
            output.update(active_indices=active,seconds=round(time.monotonic()-begin,6))
            small_json('e10_p7_core.json',output)
            print(json.dumps(item),flush=True)
            if len(active)<=20:break
        if time.monotonic()>=deadline or len(active)<=20:break
    output['active_indices']=active
    st,unit,out=is_unit(p,gens,active,30);output['final_initial']=st
    if unit:
        output['certificate_result']=certify(p,weights,active,'e10_p7_two_core_c000',max(60,600-(time.monotonic()-begin)))
        if output['certificate_result']['status']=='certified':
            p.solver.set(timeout=30000);answer=p.solver.check();output['remaining_smt_status']=str(answer)
            output['final_smt']=packed('e10_p7_two_core_final.smt2',p.solver.to_smt2())
            if answer==z3.sat:
                m=p.solver.model();output['remaining_weights']=[str(Fraction(m.eval(x).numerator_as_long(),m.eval(x).denominator_as_long())) for x in p.ws]
    output.update(seconds=round(time.monotonic()-begin,6),versions=dict(python=sys.version,z3=z3.get_version_string()))
    small_json('e10_p7_core.json',output);print(json.dumps({k:v for k,v in output.items() if k!='history'},indent=2),flush=True)

if __name__=='__main__':
    {'core':core,'slim':slim,'tpower':tpower,'normalized':normalized,
     'component':lambda:normalized(True),'linear':lambda:normalized(True,True),'r1':r1,'plain':r1_plain}[sys.argv[1]]()
