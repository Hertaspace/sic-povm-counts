#!/usr/bin/env python3.14
"""Count EVERY grid-free direct-face candidate, never treating failure as zero.

Server only. One backend subprocess at a time, at most two requested threads.
The d4–6 machine-readable gate is mandatory. Fixed seed 20261102.
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
import argparse
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import platform
import sys
import time

sys.dont_write_bytecode=True
H=Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def prime(n):
    if n<2:return False
    k=2
    while k*k<=n:
        if n%k==0:return False
        k+=1 if k==2 else 2
    return True


def good_primes(d,count=2):
    n=65537
    out=[]
    while len(out)<count:
        if (n-1)%(2*d)==0 and prime(n):out.append(n)
        n+=1
    return out


def trim_msolve(answer,tag):
    raw=answer.pop('result','')
    answer['result_bytes']=len(raw.encode())
    if raw:
        if answer.get('saturation'):
            # Large Groebner bases are transient and never synced. Preserve
            # hashes and the small exact leading-ideal length result.
            answer['large_basis_location']='transient server data directory, deleted after counting'
        else:
            cert=H/f'e28_{tag}_rur.txt'
            if len(raw.encode())<1000000:
                cert.write_text(raw)
                answer['certificate_file']=cert.name
            else:
                data=Path(os.environ.get('NF6_DATA_DIR',str(H.parent/'data')))
                data.mkdir(parents=True,exist_ok=True)
                cert=data/f'e28_{tag}_rur.txt'
                cert.write_text(raw)
                answer['certificate_remote_data_file']=str(cert)
    answer['stdout']=answer.get('stdout','')[-12000:]
    return answer


def count_one(chart,w,p,tag,args):
    from e10_face_system import count_face
    from e17_reducedness_certificates import msolve_run
    d,c,s=chart
    start=time.monotonic()
    attempt=count_face(d,c,s,list(map(Fraction,w)),p,
        timeout=args.singular_seconds,memory_gb=20,reducedness=True)
    trials=[dict(backend='Singular direct saturation and Jacobian',**attempt)]
    valid=attempt['status']=='PASS' and (attempt['dim']<0 or
        (attempt['dim']==0 and attempt['reduced'] is True))
    if valid:
        return dict(p=p,status='PASS',length=attempt['length'],reduced=True,
            backend='Singular',attempts=trials,seconds=time.monotonic()-start)
    if not args.fallback:
        return dict(p=p,status='INCOMPLETE',length=None,reduced=None,attempts=trials,
                    seconds=time.monotonic()-start)
    case=dict(d=d,c=c,s=s,w=','.join(w))
    sat=msolve_run(case,p,timeout=args.msolve_seconds,threads=args.threads,
                   verbose=1,gb=2,saturation=True)
    sat=trim_msolve(sat,tag+'_sat')
    trials.append(dict(backend='msolve native F4 saturation',**sat))
    length=sat.get('scheme_length_from_leading_ideal')
    if sat.get('status')!='DONE' or length is None:
        return dict(p=p,status='INCOMPLETE',length=length,reduced=None,attempts=trials,
                    seconds=time.monotonic()-start)
    if length==0:
        return dict(p=p,status='PASS',length=0,reduced=True,backend='msolve F4sat',
            char0_emptiness_certified=False,attempts=trials,seconds=time.monotonic()-start)
    rur=msolve_run(case,p,timeout=args.msolve_seconds,threads=args.threads,
                   verbose=1,gb=0,saturation=False)
    rur=trim_msolve(rur,tag)
    trials.append(dict(backend='msolve RUR and independent Singular identities',**rur))
    cert=rur.get('rur_verification') or {}
    valid=(rur.get('status')=='DONE' and cert.get('status')=='PASS'
           and cert.get('distinct_torus_points')==length)
    return dict(p=p,status='PASS' if valid else 'INCOMPLETE',length=length,
        reduced=True if valid else None,backend='msolve F4sat plus verified RUR',
        attempts=trials,seconds=time.monotonic()-start)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('tag',choices=['q','l1','l2','z','x1','x2'])
    ap.add_argument('--prime',type=int,action='append')
    ap.add_argument('--singular-seconds',type=float,default=60)
    ap.add_argument('--msolve-seconds',type=float,default=900)
    ap.add_argument('--threads',type=int,choices=[1,2],default=1)
    ap.add_argument('--no-fallback',dest='fallback',action='store_false')
    args=ap.parse_args()
    gate_path=H/'e14_calibration_gate.json'
    gate=json.loads(gate_path.read_text())
    assert gate['all_pass'] is True and gate['d6_boundary_total']==129024
    source_path=H/f'e03_d7_{args.tag}.json'
    source=json.loads(source_path.read_text())
    assert source['d']==7 and source['complete'] is True and source['termination']=='unsat'
    chosen=args.prime or good_primes(7)
    assert len(set(chosen))>=2 and all(prime(p) and (p-1)%14==0 and p>65536 for p in chosen)
    report=dict(format='sic-nf6-d7-direct-face-counts-v1',tag=args.tag,seed=20261102,
        gate_sha256=digest(gate_path),vertex_file=source_path.name,
        vertex_sha256=digest(source_path),parameters=vars(args),
        environment=dict(python=sys.version,platform=platform.platform()),
        sources_sha256={nm:digest(H/nm) for nm in
            ['e28_d7_face_counts.py','e10_face_system.py','e17_reducedness_certificates.py']},
        names=source['names'],zero_names=source['zero_names'],primes=chosen,
        weights=[],status='RUNNING',generic_char0_claim='certified simple special roots give generic lower bounds only')
    output=H/f'e28_d7_{args.tag}_counts.json'
    output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='weights'}),flush=True)
    for index,vertex in enumerate(source['weights']):
        w=vertex['weight']
        row=dict(index=index,weight=w,prime_counts=[])
        print(json.dumps(dict(stage='WEIGHT',tag=args.tag,index=index,weight=w)),flush=True)
        for p in chosen:
            key=f'{args.tag}_w{index:02d}_p{p}'
            ans=count_one((source['d'],source['c'],source['s']),w,p,key,args)
            row['prime_counts'].append(ans)
            print(json.dumps(dict(stage='COUNT',tag=args.tag,index=index,p=p,
                status=ans['status'],length=ans['length'],reduced=ans['reduced'])),flush=True)
        passed=all(a['status']=='PASS' and a['reduced'] is True for a in row['prime_counts'])
        lengths=[a['length'] for a in row['prime_counts']]
        row.update(two_prime_pass=passed,two_prime_lengths_agree=passed and len(set(lengths))==1,
                   char0_simple_root_lower_bound=max(lengths) if passed else None)
        report['weights'].append(row)
        output.write_text(json.dumps(report,indent=2)+'\n')
    report.update(status='PASS' if all(x['two_prime_pass'] for x in report['weights']) else 'INCOMPLETE',
        total_simple_root_lower_bound=sum(x['char0_simple_root_lower_bound'] or 0 for x in report['weights']))
    output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(stage='SUMMARY',tag=args.tag,status=report['status'],
        weights=len(report['weights']),total_simple_root_lower_bound=report['total_simple_root_lower_bound'])),flush=True)
    return 0 if report['status']=='PASS' else 2


if __name__=='__main__':raise SystemExit(main())
