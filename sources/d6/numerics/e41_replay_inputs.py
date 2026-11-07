#!/usr/bin/env python3.14
"""Read-only replay of the d6/p7 classification inputs.

Default: rerun the exhaustive support census, all 420 strata, all special
point/Jacobian/stabilizer checks and the exact 6a global-unit calculation.
--recompute-upper additionally reruns the 3456-length trace-section GB
(historically about 274 seconds and 2 GB). All output stays beside this file.
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
from pathlib import Path
from collections import Counter
import argparse,ctypes,hashlib,importlib.util,json,os,re,subprocess,time

H=Path(__file__).resolve().parent
EX=public_root(__file__)/'sources'
OLD=EX/'escape'/'numerics'
STRUCT=EX/'special-fibres'/'numerics'
PRIMES=EX/'prime-fibres'/'numerics'
NOESC=EX/'d4-upper'/'numerics'
sys.path.insert(0,str(OLD))
import e90_support_audit as S
SEED=20261031
CAS=['Singular','--no-rc',f'--random={SEED}','--cpus=1','--threads=1','--flint-threads=1','-q']


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def module(name,path):
    sp=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(sp)
    sys.modules[name]=m;sp.loader.exec_module(m);return m
def child(command,source,stem,limit):
    start=time.monotonic();peak=0;status='complete'
    with (H/(stem+'.out')).open('w') as log:
        p=subprocess.Popen(command,stdin=subprocess.PIPE if source is not None else subprocess.DEVNULL,
            stdout=log,stderr=subprocess.STDOUT,text=True,cwd=H,
            env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',OMP_NUM_THREADS='1',TMPDIR=str(H)))
        if source is not None:p.stdin.write(source);p.stdin.close()
        try:
            while p.poll() is None:
                try:peak=max(peak,S.rss(p.pid))
                except RuntimeError:pass
                if peak>=15_000_000_000:status='memory_stop'
                elif time.monotonic()-start>=limit:status='timeout'
                if status!='complete':p.kill();break
                time.sleep(.025)
            p.wait()
        except BaseException:
            if p.poll() is None:p.kill()
            p.wait();raise
    text=(H/(stem+'.out')).read_text()
    if status=='complete' and p.returncode:status='error'
    info=dict(status=status,pid=p.pid,returncode=p.returncode,seconds=round(time.monotonic()-start,6),
              sampled_peak_rss_bytes=peak,command=command,limit_seconds=limit)
    assert status=='complete',(info,text[-2000:])
    return info,text


def support():
    tick=time.monotonic();F,tau=S.finite_algebra(6,7)
    matrices=S.make_matrices(6,F,tau);constants=S.structure_constants(6,F,tau,matrices)
    minors=S.minor_polynomials(6,F,matrices,False);square=S.square_polynomials(6,F,constants,False)
    exe=H/'e41_support.bin'
    compilation,_=child([executable('c++'),'-O3','-std=c++17',str(OLD/'e90_support_audit.cpp'),'-o',str(exe)],None,'e41_compile',60)
    lines=['6']
    for family in (square[1:],minors):
        nonzero=[poly for poly in family if poly];lines.append(str(len(nonzero)))
        for poly in nonzero:
            row=S.monomials(poly);lines.append(str(len(row))+' '+' '.join(map(str,row)))
    source='\n'.join(lines)+'\n';(H/'e41_support_input.txt').write_text(source)
    census,text=child([str(exe)],source,'e41_support_census',60)
    reps=[tuple(map(int,line.split()[1:])) for line in text.splitlines() if line.startswith('ORBIT ')]
    oldrows=json.loads((OLD/'e03_support_strata.json').read_text())['rows']
    old={r['representative_mask']:r for r in oldrows if (r['d'],r['p'])==(6,7)}
    assert reps==sorted((r['representative_mask'],r['size'],r['support_size']) for r in old.values())
    assert len(reps)==420
    records=[]
    for mask,size,support_size in reps:
        src=S.stratum_source(6,7,mask,F,minors)
        status,out=child(CAS,src,'e41_stratum_last',5)
        assert not re.search(r'^\s*\?',out,re.M)
        match=re.search(r'RESULT\s+(-?\d+)\s+(-?\d+)\s+(\d+)',out);assert match
        dim,length,basis=map(int,match.groups());ref=old[mask]
        assert (dim,length)==(ref['dim'],ref['length'])
        records.append(dict(mask=mask,orbit_size=size,support_size=support_size,dim=dim,length=length,
                            input_sha256=hashlib.sha256(src.encode()).hexdigest()))
    nonempty=[r for r in records if r['dim']>=0]
    assert len(nonempty)==6 and sum(r['orbit_size'] for r in nonempty)==112
    result=dict(status='PASS',compilation=compilation,census=census,all_strata=records,
                nonempty=nonempty,seconds=round(time.monotonic()-tick,6))
    (H/'e41_support.json').write_text(json.dumps(result,indent=2)+'\n')
    return {k:v for k,v in result.items() if k!='all_strata'}


def geometry(recompute_upper):
    tick=time.monotonic();C=module('e41_census',PRIMES/'e01_census.py')
    source=C.source(6,7,reduced=True)
    oldsrc=PRIMES/'e07_d6_p7_a0b0_N.sing';oldmeta=PRIMES/'e07_d6_p7_a0b0_N.json'
    meta=json.loads(oldmeta.read_text())
    assert source==oldsrc.read_text() and hashlib.sha256(source.encode()).hexdigest()==meta['input_sha256']
    assert meta['status']=='complete' and (meta['result']['dim'],meta['result']['length'])==(0,3456)
    oldtranscript=PRIMES/'e07_d6_p7_a0b0_N.out'
    text=oldtranscript.read_text()
    assert re.search(r'RESULT dim\s+0',text) and re.search(r'RESULT length\s+3456',text)
    upper=dict(mode='accepted historical GB transcript, input regenerated and hashes checked',
               input_sha256=sha(oldsrc),transcript_sha256=sha(oldtranscript),length=3456)
    if recompute_upper:
        status,text=child(CAS,source,'e41_trace_upper_recomputed',900)
        assert not re.search(r'^\s*\?',text,re.M)
        assert re.search(r'RESULT dim\s+0',text) and re.search(r'RESULT length\s+3456',text)
        assert 'RESULT DONE' in text
        upper.update(mode='recomputed GB',child=status)
    G=module('e41_groups',STRUCT/'e02_groups.py')
    points_path=STRUCT/'e13_complete_d6.json';stable_path=STRUCT/'e02_d6_stabilizers.json'
    data=json.loads(points_path.read_text());stable=json.loads(stable_path.read_text())
    F=G.GF(7,tuple(data['modulus']));model=G.Model(F,6,data['tau'])
    points=[(tuple(row['point'][0]),tuple(row['point'][1])) for row in data['per_point']]
    assert len(points)==len(set(points))==3456;pointset=set(points);ranks=Counter()
    embedding=stable['field_descent']['embedding_table']
    for i,(point,record) in enumerate(zip(points,stable['per_point'])):
        assert all(point[0]) and all(point[1])
        assert [[embedding[x] for x in v] for v in point]==record['point']
        jac=model.jacobian_data(point)
        assert jac['equal_overlap'] and jac['t_nonzero'] and jac['on_nullfiber']
        assert (jac['rank_equal'],jac['rank_null'])==(9,10)
        ranks[(9,10)]+=1
        a,b=point;assert model.normalize_point((a[1:]+a[:1],b[1:]+b[:1])) in pointset
        assert len(record['stabilizer'])==3
        for h in record['stabilizer']:
            assert h['swap'] is False
            if h['projective_order']!=1:assert (h['projective_order'],h['trace_mod_d'])==(3,5)
    groupcheck=G.verify_stabilizer_certificate(stable)
    assert groupcheck['verified'] and groupcheck['ordinary_group_order']==5184
    assert len(stable['extended_orbits'])==1 and len(stable['ordinary_orbits'])==2
    result=dict(status='PASS',trace_upper=upper,points=3456,local_algebra='k[N]/(N^2)',
                full_special_length=6912,all_point_jacobians=str(dict(ranks)),
                all_coordinate_units=True,cyclic_shift_closed=True,group_replay=groupcheck,
                actual_nonidentity_stabilizer_orders_and_traces=[3,5],
                input_hashes={str(path):sha(path) for path in [points_path,stable_path,STRUCT/'e02_groups.py',oldsrc,oldmeta,oldtranscript]},
                seconds=round(time.monotonic()-tick,6))
    (H/'e41_geometry.json').write_text(json.dumps(result,indent=2)+'\n');return result


def seed():
    tick=time.monotonic();path=NOESC/'e20_hermitian_6a.gp';source=path.read_text()
    status,text=child([executable('gp'),'-fq'],source,'e41_seed_units',180)
    assert 'STAGE_COMPLETE|1' in text and not re.search(r'\*\*\*.*(error|Error|at top-level)',text)
    rows=[];unitrows=[]
    for line in text.splitlines():
        if line.startswith('SQUARED_PHASE_POLYNOMIAL|'):
            ci,index,coeff=json.loads(line.split('|',1)[1]);assert coeff[0]==1 and abs(coeff[-1])==1
            rows.append(dict(root_class=ci,label_index=index,degree=len(coeff)-1,monic_unit=True))
        elif line.startswith('ALL_UPPER_PRIME_UNIT|'):
            row=json.loads(line.split('|',1)[1]);assert row[1:]==[7,1,0,0];unitrows.append(row)
    assert len(rows)==len(unitrows)==13
    assert re.search(r'RANK_ONE_HERMITIAN_TRACE_ONE\|\[6,\s*36,\s*36,\s*1\]',text)
    result=dict(status='PASS',source_sha256=sha(path),child=status,root_classes=rows,
                squared_phases='all 35 nonzero labels covered by 13 root-unit classes',
                exact_seed='rank one, Hermitian, trace one, all signed integer-label SIC equations',
                seconds=round(time.monotonic()-tick,6))
    (H/'e41_seed.json').write_text(json.dumps(result,indent=2)+'\n');return result


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--stage',choices=['all','support','geometry','seed'],default='all')
    ap.add_argument('--recompute-upper',action='store_true');args=ap.parse_args()
    out=dict(status='IN_PROGRESS',seed=SEED,stages={},all_writes_in=str(H));start=time.monotonic()
    for name,fn in [('support',support),('geometry',lambda:geometry(args.recompute_upper)),('seed',seed)]:
        if args.stage not in ('all',name):continue
        print('START',name,flush=True);result=fn();out['stages'][name]=result
        print('PASS',name,'seconds',result['seconds'],flush=True)
        (H/'e41_replay_inputs.json').write_text(json.dumps(out,indent=2)+'\n')
    out.update(status='PASS',seconds=round(time.monotonic()-start,6),recomputed_trace_upper=args.recompute_upper)
    (H/'e41_replay_inputs.json').write_text(json.dumps(out,indent=2)+'\n')
    print('ALL_INPUT_REPLAYS_PASS',out['seconds'],flush=True)


if __name__=='__main__':main()
