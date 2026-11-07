#!/usr/bin/env python3.14
"""Aggregate exact cone lower bounds; the supplied spur input stays numerical."""

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
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode=True
H=Path(__file__).resolve().parent
MULT={'q':3,'z':3,'x1':2,'x2':6,'l1':6,'l2':6}
OLD={'q':4184,'z':96,'x1':8,'x2':32,'l1':120,'l2':48}


def main():
    from e02_sparse_volume import verify_certificate
    from e04_d7_sparse_volumes import load_certificate
    from e10_face_system import build_chart,face_at
    volume_path=H/'e04_d7_sparse_volumes.json'
    volumes=json.loads(volume_path.read_text())
    assert volumes['status']=='PASS'
    volume_map={(x['tag'],x['index']):x for x in volumes['weights']}
    assert len(volume_map)==len(volumes['weights']), 'duplicate volume key'
    rows=[]
    complete=True
    exact_direct=True
    certified_units=0
    for tag in MULT:
        path=H/f'e28_d7_{tag}_counts.json'
        vertex=H/f'e03_d7_{tag}.json'
        if not path.exists():
            rows.append(dict(tag=tag,status='MISSING'))
            complete=False
            continue
        data=json.loads(path.read_text())
        source=json.loads(vertex.read_text())
        assert hashlib.sha256(vertex.read_bytes()).hexdigest()==data['vertex_sha256']
        assert len(data['weights'])==len(source['weights']) or data['status']!='PASS'
        indices=[x['index'] for x in data['weights']]
        assert len(set(indices))==len(indices), 'duplicate count index'
        assert all(0<=i<len(source['weights']) for i in indices)
        if data['status']=='PASS':assert sorted(indices)==list(range(len(source['weights'])))
        amount=0
        table=[]
        chart=build_chart(source['d'],source['c'],source['s'])
        for w in data['weights']:
            assert w['weight']==source['weights'][w['index']]['weight']
            good=[p for p in w['prime_counts'] if p['status']=='PASS' and p['reduced'] is True]
            lower=max((p['length'] for p in good),default=0)
            twoprime=len({p['p'] for p in good})>=2
            complete=complete and twoprime
            amount+=lower
            volume=volume_map[tag,w['index']]
            cert_path=H/volume['certificate_file']
            assert hashlib.sha256(cert_path.read_bytes()).hexdigest()==volume['certificate_sha256']
            cert=load_certificate(cert_path)
            assert cert['vertex_sha256']==data['vertex_sha256']
            assert cert['weight']==w['weight'] and cert['names']==source['names']
            assert cert['certificate']['points']==list(map(list,face_at(chart,w['weight']).support))
            bound=verify_certificate(cert['certificate'])
            assert bound==cert['result']==volume['volume_result']
            upper=bound['normalized_volume']
            assert lower<=upper
            exact=twoprime and lower==upper
            exact_direct=exact_direct and exact
            table.append(dict(weight=w['weight'],simple_char0_lower=lower,
                exact_normalized_volume_upper=upper,generic_char0_face_count_exact=exact,
                volume_certificate=cert_path.name,
                two_prime_pass=twoprime,prime_counts=[dict(p=p['p'],length=p['length'],
                    status=p['status'],reduced=p['reduced']) for p in w['prime_counts']]))
        complete=complete and data['status']=='PASS' and source['complete']
        certified_units+=MULT[tag]*amount
        rows.append(dict(tag=tag,status=data['status'],candidates=len(source['weights']),
            covered_vertex_weights=len(data['weights']),representative_simple_path_lower=amount,
            unit_multiplier=MULT[tag],new_units_relative_to_supplied=MULT[tag]*(amount-OLD[tag]),
            weights=table,source=path.name,source_sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
    bezout=2**12*math.comb(12,6)
    spur_numerical=2080736
    conditional=bezout-spur_numerical-112*certified_units
    out=dict(format='sic-nf6-d7-cone-summary-v1',seed=20261102,
        all_six_two_prime_nondegenerate=complete,representatives=rows,
        all_generic_char0_direct_face_counts_exact=complete and exact_direct,
        certified_boundary_path_lower=112*certified_units,certified_units=certified_units,
        supplied_units=14056,new_units_relative_to_supplied=certified_units-14056,
        bezout=bezout,spur_input=dict(count=spur_numerical,nature='NUMERICAL, NOT CERTIFIED HERE'),
        bound_CONDITIONAL_on_spur=conditional,strict_target=49392,
        conditional_target_met=conditional<49392,
        remaining_units_to_strict_target=max(0,(conditional-49392)//112+1),
        char0_exact_total_count_claim=False,
        scope='All candidate weights for isolated GLOBAL direct faces only; no coverage of higher-layer Puiseux paths.')
    (H/'e29_d7_summary.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))


if __name__=='__main__':main()
