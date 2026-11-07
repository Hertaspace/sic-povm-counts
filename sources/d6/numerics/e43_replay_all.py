#!/usr/bin/env python3.14
"""Serial entry point for the complete d6 certificate replay package.

Default reruns the five listed verification scripts. --records-only checks
their already-produced records and source hashes. --recompute-upper also
reruns the historical special-fibre trace-section GB in the new directory.
Run this entry point only in a fresh replay workspace.
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
import argparse,hashlib,json,os,signal,subprocess,time
H=Path(__file__).resolve().parent

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def run(name,extra):
    command=[sys.executable,'-B',str(H/name)]+extra;tick=time.monotonic()
    with (H/('e43_'+Path(name).stem+'.out')).open('w') as log:
        p=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,cwd=H,
            env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',OMP_NUM_THREADS='1',TMPDIR=str(H)))
        try:code=p.wait(timeout=1500)
        except BaseException:
            if p.poll() is None:
                p.send_signal(signal.SIGINT)
                try:p.wait(timeout=10)
                except subprocess.TimeoutExpired:p.kill();p.wait()
            raise
    assert code==0,(name,code)
    return dict(script=name,command=command,seconds=round(time.monotonic()-tick,6))

def verify_records(records_only=False):
    names=['e40_replay_boundary.json','e41_replay_inputs.json',
           'e42_replay_known_orbits.out' if records_only else 'e43_e42_replay_known_orbits.out',
           'e90_component_audit.json','e90_r1_plain_audit.json']
    records={name:json.loads((H/name).read_text()) for name in names}
    assert records[names[0]]['status']=='PASS'
    assert records[names[0]]['identity_count']==147 and records[names[0]]['complete_boundary_coverage']
    assert len(records[names[0]]['covers'])==6 and all(c['status']=='unsat' for c in records[names[0]]['covers'])
    assert all(not c['uses_e31'] and not c['uses_saved_smt'] for c in records[names[0]]['covers'])
    assert records[names[1]]['status']=='PASS' and set(records[names[1]]['stages'])=={'support','geometry','seed'}
    assert records[names[2]]['status']=='CERTIFIED'
    assert records[names[3]]['status']==records[names[4]]['status']=='PASS'
    hashes={}
    for identity in records[names[0]]['identities']:hashes.update(identity['hashes'])
    hashes.update(records[names[0]]['source_hashes'])
    hashes.update(records[names[1]]['stages']['geometry']['input_hashes'])
    for path,expected in hashes.items():assert sha(Path(path))==expected,path
    seedpath=public_root(__file__)/'sources/d4-upper/numerics'/'e20_hermitian_6a.gp'
    assert sha(seedpath)==records[names[1]]['stages']['seed']['source_sha256']
    return dict(status='PASS',records={name:sha(H/name) for name in names},
                checked_dependency_hashes=len(hashes)+1,identity_count=147,six_fresh_covers='UNSAT',
                full_special_points=3456,full_complex_points=6912,
                upper_bound_recomputed=records[names[1]]['recomputed_trace_upper'])

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--records-only',action='store_true');ap.add_argument('--recompute-upper',action='store_true')
    args=ap.parse_args();assert not(args.records_only and args.recompute_upper)
    if args.records_only:
        raise SystemExit('Inspect historical adapted records with replay/run.py d6 --records-only; they do not certify edited programs.')
    start=time.monotonic();stages=[]
    if not args.records_only:
        for name,extra in [('e40_replay_boundary.py',[]),('e41_replay_inputs.py',['--recompute-upper'] if args.recompute_upper else []),
                           ('e42_replay_known_orbits.py',[]),('e90_component_audit.py',[]),('e90_r1_plain_audit.py',[])]:
            print('REPLAY',name,flush=True);stages.append(run(name,extra))
    result=verify_records(args.records_only);result.update(stages=stages,records_only=args.records_only,seconds=round(time.monotonic()-start,6),
                                         own_script_sha256=sha(Path(__file__)))
    (H/'e43_replay_all.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':main()
