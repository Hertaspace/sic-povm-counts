#!/usr/bin/env python3.14
"""Primary exhaustive projective-q separation of certified orbit roots.

Run remotely with the isolated python-flint target. Only exact certificate
boxes enter the invariant computation; numerical monodromy coordinates do not.
The order and all hashes can be replayed by the independent e42 implementation.
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
from pathlib import Path
import random
import sys
import time

sys.dont_write_bytecode=True
H=Path(__file__).resolve().parent
SEED=20261102


def sha(path):
    dig=hashlib.sha256()
    with open(path,'rb') as handle:
        for block in iter(lambda:handle.read(1024**2),b''):dig.update(block)
    return dig.hexdigest()


def resolve(name,base):
    p=Path(name)
    if p.exists():return p
    p=base/Path(name).name
    if p.exists():return p
    raise FileNotFoundError(name)


def check_matrix_binding(header,header_path):
    raw_path=resolve(header['matrix_file'],header_path.parent)
    assert sha(raw_path)==header['matrix_sha256']
    raw=json.loads(raw_path.read_text())
    assert raw['d']==header['d'] and raw['q_labels']==header['q_labels']
    scale=int(header['M']['scale'])
    unit=Fraction(2)**scale
    for r,row in enumerate(header['M']['rows']):
        for c,z in enumerate(row):
            assert int(z[0])*unit==Fraction(int(raw['real_numerators'][r][c]),int(raw['denominator']))
            assert int(z[1])*unit==Fraction(int(raw['imag_numerators'][r][c]),int(raw['denominator']))
    return raw_path


def main():
    if not __debug__:raise RuntimeError('optimized Python disables certificate assertions')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--manifest',type=Path,required=True,help='e41 individual-root manifest')
    ap.add_argument('--basis',type=Path)
    ap.add_argument('--precision',type=int,default=512)
    ap.add_argument('--interval-scale',type=int,default=-256)
    ap.add_argument('--tries',type=int,default=16)
    ap.add_argument('--output-prefix',default=None)
    args=ap.parse_args()
    from flint import acb,ctx
    from e41_certify import CertifiedSystem,box_from_certificate,outward_dyadic
    ctx.prec=args.precision
    try:ctx.threads=1
    except AttributeError:pass
    started=time.monotonic()
    source_sha=sha(args.manifest)
    individual=json.loads(args.manifest.read_text())
    d=int(individual['d'])
    header_path=resolve(individual['header_file'],args.manifest.parent)
    assert sha(header_path)==individual['header_sha256']
    header=json.loads(header_path.read_text())
    raw_matrix_path=check_matrix_binding(header,header_path)
    basis_path=args.basis or H/f'e43_d{d}_q_basis.json'
    basis=json.loads(basis_path.read_text())
    assert basis['d']==d and basis['q_labels']==header['q_labels']
    assert basis['coefficientwise_spanning_identities_verified'] is True
    indices=basis['raw_q_indices'];k=len(indices)
    assert k==basis['rank']==({6:12,7:15}[d])
    system=CertifiedSystem(header)
    identities=[];qvalues=[];certificate_files=[];seen=set()
    for entry in individual['chunks']:
        path=resolve(entry['file'],args.manifest.parent)
        expected=entry['sha256'];assert sha(path)==expected
        certificate_files.append(dict(file=path.name,sha256=expected))
        local_ids=[]
        for line in path.read_text().splitlines():
            if not line.strip():continue
            record=json.loads(line);identity=int(record['id'])
            assert identity not in seen,'duplicate certificate id'
            seen.add(identity);local_ids.append(identity)
            q=system.q_balls(box_from_certificate(record))
            assert any(not z.contains(0) for z in q),'off-base not established on box'
            identities.append(identity);qvalues.append([q[j] for j in indices])
        assert len(local_ids)==entry['count'] and local_ids==entry['ids']
        assert sha(path)==expected,'certificate changed while reading'
    n=len(identities)
    assert n==individual['certified_representatives'] and n>0
    print(json.dumps(dict(stage='q_boxes_loaded',d=d,roots=n,basis_dimension=k,
                         seconds=time.monotonic()-started)),flush=True)
    rand=random.Random(SEED+d)
    failures=[]
    for trial in range(args.tries):
        # A Gaussian-integer projection is proposed, never assumed injective.
        numerator=[[rand.randrange(-9,10),rand.randrange(-9,10)] for _ in range(k)]
        denominator=[[rand.randrange(-9,10),rand.randrange(-9,10)] for _ in range(k)]
        aa=[acb(*z) for z in numerator];bb=[acb(*z) for z in denominator]
        intervals=[]
        try:
            for identity,q in zip(identities,qvalues):
                num=sum((a*z for a,z in zip(aa,q)),acb(0))
                den=sum((a*z for a,z in zip(bb,q)),acb(0))
                if den.contains(0):raise ValueError(f'denominator not separated from zero at id {identity}')
                value=(num/den).real
                lo,hi=map(int,outward_dyadic(value,args.interval_scale))
                intervals.append((lo,hi,identity))
            intervals.sort(key=lambda x:(x[0]+x[1],x[2]))
            gaps=[right[0]-left[1] for left,right in zip(intervals,intervals[1:])]
            if any(g<=0 for g in gaps):
                bad=[(left[2],right[2],str(right[0]-left[1]))
                     for left,right in zip(intervals,intervals[1:]) if right[0]<=left[1]]
                raise ValueError('projection intervals overlap '+json.dumps(bad[:20]))
        except Exception as exc:
            failures.append(dict(trial=trial,error=repr(exc)))
            print(json.dumps(dict(stage='projection_rejected',**failures[-1])),flush=True)
            continue
        break
    else:
        raise RuntimeError('No certified separating projection: '+json.dumps(failures))
    order=[row[2] for row in intervals]
    assert len(set(order))==n
    prefix=args.output_prefix or f'e43_d{d}_separation'
    output=H/f'{prefix}.json'
    report=dict(schema='spur-invariant-separation-v1',d=d,seed=SEED,
        header_file=header_path.name,header_sha256=sha(header_path),
        matrix_file=raw_matrix_path.name,matrix_sha256=header['matrix_sha256'],
        system_file=raw_matrix_path.name,system_sha256=sha(raw_matrix_path),
        basis_file=basis_path.name,basis_sha256=sha(basis_path),
        individual_manifest_file=args.manifest.name,individual_manifest_sha256=source_sha,
        certificate_files=certificate_files,raw_q_indices=indices,
        functional_num=numerator,functional_den=denominator,order=order,
        certified_orbits=n,group_order=2*d*d,distinct_point_lower_bound=n*2*d*d,
        interval_scale=args.interval_scale,minimum_scaled_adjacent_gap=str(min(gaps)) if gaps else None,
        primary_precision_bits=args.precision,primary_projection_trial=trial,
        primary_all_adjacent_strict=True,all_orbit_pairs_separated=True,
        previous_projection_failures=failures,
        meaning='One strictly ordered real projective-q invariant separates every pair of certified G orbits; root and freeness certificates are separate.',
        seconds=round(time.monotonic()-started,6),python=sys.version,
        checker_sha256=sha(__file__))
    assert sha(args.manifest)==source_sha,'individual manifest changed during separation'
    assert sha(header_path)==individual['header_sha256'],'header changed during separation'
    assert sha(raw_matrix_path)==header['matrix_sha256'],'exact matrix changed during separation'
    for entry in certificate_files:
        assert sha(resolve(entry['file'],args.manifest.parent))==entry['sha256']
    encoded=json.dumps(report,indent=2)+'\n'
    assert len(encoded.encode())<1024**2,'split separation manifest before syncing'
    output.write_text(encoded)
    print(json.dumps({key:value for key,value in report.items()
                     if key not in ('order','certificate_files')},indent=2),flush=True)
    if d==7 and n>21232:
        raise RuntimeError('CERTIFIED ORBIT COUNT EXCEEDS 21232: contradiction must be reported')


if __name__=='__main__':main()
