#!/usr/bin/env python3.14
"""Freeze one root-certificate set and obtain an independently checked count.

Server only. Each invocation is a finite batch, never a wait/poll loop. The
replay source is copied to an immutable task data path before workers start.
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
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
sys.dont_write_bytecode=True
H=Path(__file__).resolve().parent


def digest(path):
    out=hashlib.sha256()
    with open(path,'rb') as handle:
        for block in iter(lambda:handle.read(1024**2),b''):out.update(block)
    return out.hexdigest()


def immutable_copy(source,target):
    value=Path(source).read_bytes()
    if target.exists():
        assert target.read_bytes()==value,'immutable snapshot already differs'
    else:target.write_bytes(value)
    return hashlib.sha256(value).hexdigest()


def normalize(entries):
    out={Path(name).name:sha for name,sha in entries.items()}
    assert len(out)==len(entries),'ambiguous duplicate basename'
    return out


def run(command,log):
    print(json.dumps(dict(stage='run',command=command,log=str(log))),flush=True)
    with open(log,'w') as handle:
        answer=subprocess.run(command,stdout=handle,stderr=subprocess.STDOUT)
    assert answer.returncode==0,f'subcheck failed exit={answer.returncode}: {log}'


def main():
    if not __debug__:raise RuntimeError('optimized Python disables certificate assertions')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--d',type=int,choices=[6,7],required=True)
    ap.add_argument('--tag',required=True,help='unique immutable snapshot tag')
    ap.add_argument('--manifest',type=Path)
    ap.add_argument('--workers',type=int,choices=[1,2,3,4],default=4)
    ap.add_argument('--bits',type=int,default=384)
    args=ap.parse_args()
    assert args.tag and all(c.isalnum() or c in '_-' for c in args.tag)
    started=time.monotonic();d=args.d
    live=args.manifest or H/f'e41_d{d}_manifest.json'
    prefix=f'e44_d{d}_{args.tag}'
    snapshot=H/f'{prefix}_root_snapshot.json'
    snapshot_sha=immutable_copy(live,snapshot)
    individual=json.loads(snapshot.read_text())
    assert individual['d']==d
    header=H/Path(individual['header_file']).name
    assert digest(header)==individual['header_sha256']
    files=[H/Path(c['file']).name for c in individual['chunks']]
    assert len(files)==len(set(files)) and files
    expected={p.name:c['sha256'] for p,c in zip(files,individual['chunks'])}
    ids=[]
    for path,chunk in zip(files,individual['chunks']):
        assert digest(path)==chunk['sha256']
        ids.extend(chunk['ids'])
    assert len(ids)==len(set(ids))==individual['certified_representatives']
    expected_ids_sha=hashlib.sha256(json.dumps(sorted(ids),separators=(',',':')).encode()).hexdigest()
    data=Path(os.environ.get('NF6_DATA_DIR',str(H.parent/'data')))
    data.mkdir(parents=True,exist_ok=True)
    checker=data/f'{prefix}_independent_checker.py'
    checker_sha=immutable_copy(H/'e42_spur_independent.py',checker)
    root_result=H/f'{prefix}_roots.json'
    run([sys.executable,str(checker),'--header',str(header),'--certificates',
         *map(str,files),'--workers',str(args.workers),'--bits',str(args.bits),
         '--output',str(root_result)],H/f'{prefix}_roots.out')
    sep_prefix=f'{prefix}_separation'
    run([sys.executable,str(H/'e43_spur_separation.py'),'--manifest',str(snapshot),
         '--output-prefix',sep_prefix],H/f'{prefix}_separation.out')
    sep_manifest=H/f'{sep_prefix}.json'
    sep_result=H/f'{prefix}_separation_independent.json'
    run([sys.executable,str(checker),'--separation',str(sep_manifest),
         '--bits',str(args.bits),'--output',str(sep_result)],H/f'{prefix}_separation_independent.out')
    roots=json.loads(root_result.read_text());separation=json.loads(sep_result.read_text())
    primary=json.loads(sep_manifest.read_text())
    assert roots['passed'] and separation['passed'] and separation['all_pairwise_separation']
    assert roots['checked_representatives']==separation['checked_representatives']==len(ids)
    assert roots['representative_ids_sha256']==separation['representative_ids_sha256']==expected_ids_sha
    assert roots['header_sha256']==separation['header_sha256']==individual['header_sha256']
    assert normalize(roots['certificate_sha256'])==normalize(separation['certificate_sha256'])==expected
    assert roots['matrix_binding']['sha256']==separation['matrix_binding']['sha256']
    assert roots['checker_sha256']==separation['checker_sha256']==checker_sha
    assert roots['freeness_checks']==len(ids)*(2*d*d-1)
    assert digest(snapshot)==snapshot_sha and digest(checker)==checker_sha
    assert separation['manifest_sha256']==digest(sep_manifest)
    assert digest(header)==individual['header_sha256']
    matrix_path=H/Path(roots['matrix_binding']['file']).name
    assert digest(matrix_path)==roots['matrix_binding']['sha256']
    assert digest(H/Path(primary['basis_file']).name)==primary['basis_sha256']
    for path in files:assert digest(path)==expected[path.name]
    orbit_size=2*d*d;N=len(ids)*orbit_size
    result=dict(schema='spur-independent-count-v1',d=d,seed=20261102,passed=True,
        certified_orbits=len(ids),orbit_size=orbit_size,certified_spur_lower_bound=N,
        exact_matrix_sha256=roots['matrix_binding']['sha256'],
        root_snapshot_file=snapshot.name,root_snapshot_sha256=snapshot_sha,
        header_file=header.name,header_sha256=individual['header_sha256'],
        root_checker_result=root_result.name,root_checker_result_sha256=digest(root_result),
        separation_manifest=sep_manifest.name,separation_manifest_sha256=digest(sep_manifest),
        separation_checker_result=sep_result.name,separation_checker_result_sha256=digest(sep_result),
        checker_source_file=str(checker),checker_source_sha256=checker_sha,
        representative_ids_sha256=expected_ids_sha,
        q_basis_indices=primary['raw_q_indices'],q_basis_sha256=primary['basis_sha256'],
        root_exist_unique=True,jacobian_nonsingular=True,all_off_base=True,
        complete_nonidentity_freeness_checks=True,all_orbit_pairs_distinct=True,
        integer_interval_bits=args.bits,workers=args.workers,
        meets_d7_strict_threshold=(N>=2064273) if d==7 else None,
        meets_d7_full_target=(N==2080736) if d==7 else None,
        exceeds_d7_budget=(len(ids)>21232) if d==7 else None,
        conditional_upper_after_cone_bound=2113664-N if d==7 else None,
        no_monodromy_completeness_assumed=True,
        seconds=round(time.monotonic()-started,6),python=sys.version)
    out=H/f'{prefix}_count.json';out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)
    if d==7 and len(ids)>21232:
        raise RuntimeError('Certified count exceeds the known-point/cone budget. Immediate contradiction report required.')


if __name__=='__main__':main()
