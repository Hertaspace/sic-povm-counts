#!/usr/bin/env python3.14
"""Reverify a compact d6 surface certificate, using one remote Singular job.

Usage on cluster: python e19_verify_saved.py --p 65881
This launches Singular. Under the user's remote-only compute rule, never run
this verifier on the local machine. The certificate itself is below 1 MiB.
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
from pathlib import Path
import sys
sys.dont_write_bytecode=True
from e10_face_system import SEED,build_chart,face_at,generic_square
from e11_known_calibration import CASES
from e17_reducedness_certificates import verify_rur


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--p',type=int,required=True)
    ap.add_argument('--certificate',type=Path)
    ap.add_argument('--timeout',type=float,default=600)
    args=ap.parse_args()
    root=Path(__file__).resolve().parent
    path=args.certificate or root/f'e18_surface_rur_p{args.p}.txt'
    text=path.read_text()
    case=CASES['d6_surface1920']
    face=face_at(build_chart(6,0,1,args.p),case['w'].split(','))
    check=verify_rur(text,face,generic_square(face),timeout=args.timeout)
    satpath=root/f'e13_remote_surface_sat_p{args.p}.out'
    sat=json.loads(satpath.read_text().splitlines()[-1]) if satpath.exists() else {}
    length=sat.get('scheme_length_from_leading_ideal')
    reduced=(check['status']=='PASS' and check['distinct_torus_points']==length)
    print(json.dumps(dict(status='PASS' if reduced else 'FAIL_OR_INCOMPLETE',seed=SEED,p=args.p,
        certificate=path.name,certificate_sha256=hashlib.sha256(text.encode()).hexdigest(),
        saturation_length=length,distinct_torus_points=check['distinct_torus_points'],
        reduced=reduced,verification=check,
        proof='A surjection from the saturated quotient onto the squarefree eliminant algebra has equal dimension and is therefore an isomorphism.'),sort_keys=True))


if __name__=='__main__':main()
