#!/usr/bin/env python3.14
"""Independently substitute every saved d7 RUR into reconstructed face inputs.

Server only because this starts Singular. Does not repeat Groebner searches.
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
import hashlib
import json
from pathlib import Path
import re
import sys
sys.dont_write_bytecode=True
from e10_face_system import build_chart,face_at,generic_square,SEED
from e17_reducedness_certificates import verify_rur

H=Path(__file__).resolve().parent


def main():
    gate=json.loads((H/'e14_calibration_gate.json').read_text())
    assert gate['all_pass']
    records=[]
    for path in sorted(H.glob('e28_*_rur.txt')):
        match=re.fullmatch(r'e28_(q|l1|l2|z|x1|x2)_w(\d+)_p(\d+)_rur.txt',path.name)
        if not match:continue
        tag,index,p=match[1],int(match[2]),int(match[3])
        source=json.loads((H/f'e03_d7_{tag}.json').read_text())
        counted=json.loads((H/f'e28_d7_{tag}_counts.json').read_text())
        expected=next(x['length'] for x in counted['weights'][index]['prime_counts'] if x['p']==p)
        assert source['weights'][index]['weight']==counted['weights'][index]['weight']
        face=face_at(build_chart(7,source['c'],source['s'],p),source['weights'][index]['weight'])
        result=verify_rur(path.read_text(),face,generic_square(face),timeout=300)
        assert result['status']=='PASS' and result['distinct_torus_points']==expected
        record=dict(file=path.name,tag=tag,index=index,p=p,seed=SEED,
            certificate_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
            expected_saturated_length=expected,**result)
        records.append(record)
        print(json.dumps(record),flush=True)
    assert records,'No saved fallback certificates found'
    report=dict(status='PASS',certificates=len(records),records=records,
                scheme_lengths_recomputed=False,all_substitutions_to_original_face=True)
    (H/'e31_d7_rur_replay.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(status='PASS',certificates=len(records))),flush=True)


if __name__=='__main__':main()
