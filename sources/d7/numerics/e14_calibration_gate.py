#!/usr/bin/env python3.14
"""Aggregate independent grid-free covers and two-prime scheme counts.

This is a read-only, sub-second aggregator. It launches no algebra backend.
all_pass permits d7 direct-face computations only after every d4–6 gate passes.
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
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
from e11_known_calibration import CASES

ROOT=Path(__file__).resolve().parent
GROUPS={
 'd4_point':['d4_point16'],
 'd5_point':['d5_point64','d5_point36'],
 'd5_line':['d5_line8'],
 'd6_point':['d6_point256'],
 'd6_line':['d6_line32'],
 'd6_line_a':['d6_lineA32'],
 'd6_surface':['d6_surface1920'],
 'd6_embedded_line':[],
}


def read_jsonlines(path):
    if not path.exists():return []
    out=[]
    for line in path.read_text().splitlines():
        try:out.append(json.loads(line))
        except json.JSONDecodeError:pass
    return out


def canonical(weight):return tuple(str(Fraction(w)) for w in weight)


def last_result(path):
    entries=read_jsonlines(path)
    return entries[-1] if entries else {}


def gate():
    vertex_checks=[]
    for tag,cases in GROUPS.items():
        path=ROOT/f'e01_{tag}.json'
        saved=json.loads(path.read_text()) if path.exists() else {}
        actual=sorted(canonical(item['weight']) for item in saved.get('weights',[]))
        expected=sorted(canonical(CASES[c]['w'].split(',')) for c in cases)
        representative=CASES[cases[0]] if cases else dict(d=6,c=0,s=1)
        ok=(saved.get('complete') is True and saved.get('termination')=='unsat'
            and saved.get('full_vertex_count')==len(cases) and actual==expected
            and all(saved.get(key)==representative[key] for key in ('d','c','s')))
        vertex_checks.append(dict(tag=tag,pass_gate=ok,source=path.name,
            sha256=hashlib.sha256(path.read_bytes()).hexdigest() if path.exists() else None,
            complete=saved.get('complete'),termination=saved.get('termination'),
            candidate_count=saved.get('full_vertex_count'),expected_count=len(cases),weights_match=actual==expected))
    known=read_jsonlines(ROOT/'e11_known_calibration.out')
    ffchecks=[]
    for name,case in CASES.items():
        if name=='d6_surface1920':continue
        rr=[r for r in known if r.get('name')==name and r.get('calibration_pass') is True
            and r.get('dim')==0 and r.get('length')==case['expected'] and r.get('reduced') is True
            and canonical(r.get('w',[]))==canonical(case['w'].split(','))]
        pp=sorted(set(r['p'] for r in rr))
        ffchecks.append(dict(name=name,pass_gate=len(pp)>=2,primes=pp,
            length=case['expected'],reduced_all=all(r['reduced'] for r in rr),
            evidence='Singular saturation, exact quotient length and invertible square Jacobian',
            source='e11_known_calibration.out',input_sha256=[r['source_sha256'] for r in rr]))
    surface=[]
    for p in [65761,65881]:
        satpath=ROOT/f'e13_remote_surface_sat_p{p}.out'
        rurpath=ROOT/f'e13_remote_surface_rur_p{p}.out'
        reverified=ROOT/f'e17_remote_surface_rur_p{p}.out'
        if (last_result(reverified).get('rur_verification') or {}).get('status')=='PASS':
            rurpath=reverified
        sat=last_result(satpath);rur=last_result(rurpath)
        verify=rur.get('rur_verification') or {}
        ok=(sat.get('status')=='DONE' and sat.get('saturation') is True
            and sat.get('p')==p and rur.get('p')==p
            and sat.get('scheme_length_from_leading_ideal')==1920
            and rur.get('status')=='DONE' and verify.get('status')=='PASS'
            and verify.get('distinct_torus_points')==1920
            and canonical(rur.get('weight',[]))==canonical(CASES['d6_surface1920']['w'].split(',')))
        surface.append(dict(p=p,pass_gate=ok,
            saturated_length=sat.get('scheme_length_from_leading_ideal'),
            verified_distinct_torus_points=verify.get('distinct_torus_points'),
            reduced=True if ok else None,
            saturation_source=satpath.name,rur_source=rurpath.name,
            saturation_input_sha256=sat.get('input_sha256'),saturated_basis_sha256=sat.get('result_sha256'),
            rur_input_sha256=rur.get('input_sha256'),rur_output_sha256=rur.get('result_sha256'),
            rur_verification_source_sha256=verify.get('source_sha256'),
            rur_checks=verify.get('checks'),saturation_status=sat.get('status'),rur_status=rur.get('status')))
    all_pass=(all(x['pass_gate'] for x in vertex_checks+ffchecks+surface))
    ans=dict(format='sic-nf6-calibration-gate-v1',seed=20261102,all_pass=all_pass,
        status='PASS' if all_pass else 'PENDING_OR_FAILED',
        scope='All isolated nondegenerate direct GLOBAL-minimum faces with strictly positive transverse and zero stratum valuations; no higher-layer completeness claim.',
        grid_free_vertex_covers=vertex_checks,two_prime_finite_field_counts=ffchecks,
        surface_two_prime_certificates=surface,
        d6_boundary_total=129024 if all_pass else None,
        d6_boundary_formula='288*256+288*32+24*1920=129024',
        char0_claim='Etale special solutions lift and give a characteristic-zero lower bound for the lifted coefficient system; no automatic equality of total affine characteristic-zero degree.',
        no_d7_authorization_until_gate_pass=True)
    path=ROOT/'e14_calibration_gate.json'
    path.write_text(json.dumps(ans,indent=2,sort_keys=True)+'\n')
    return ans


if __name__=='__main__':
    result=gate()
    print(json.dumps(result,indent=2,sort_keys=True))
