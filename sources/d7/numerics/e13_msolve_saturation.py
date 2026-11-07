#!/usr/bin/env python3.14
"""Native F4 saturation backend; exact finite-field Groebner bases via msolve.

Temporary potentially large bases remain in a temporary directory. One msolve
process and subsequent Singular verifier are run sequentially. At most two
CPU threads, selected explicitly by --threads (default one).
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
import ast
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import shutil
import sys
import tempfile
import time
sys.dont_write_bytecode=True
from e10_face_system import SEED,build_chart,face_at,generic_square,poly_string
from e11_known_calibration import CASES


def univariate_string(coeffs):
    return '+'.join(f'{int(c)}*tt^{i}' for i,c in enumerate(coeffs) if c) or '0'


def verify_rur(result,face,polys,timeout=600):
    """Independently authenticate a rational parametrization using Singular.

    The squarefree degree D eliminant, invertible coordinate denominator,
    input identities, invertible torus coordinates, and separating form=tt
    certify D DISTINCT geometric torus roots. Comparing D to the independent
    saturated monomial quotient length proves reducedness without trusting
    msolve's own squarefree-only solution count as a scheme length.
    """
    parsed=ast.literal_eval(result.strip().rstrip(':;'))
    if parsed[0]!=0:raise ValueError('no finite RUR')
    data=parsed[1]
    p,nvars,degree,order,linear,versioned=data
    if int(p)!=face.chart.p:raise ValueError('RUR characteristic mismatch')
    if versioned[0]!=1:raise ValueError('unsupported RUR version')
    eliminant,denominator,coordinates=versioned[1]
    if eliminant[0]!=len(eliminant[1])-1:raise ValueError('bad degree')
    if len(coordinates)!=nvars-1:raise ValueError('wrong coordinate count')
    # In the absence of an auxiliary linear form, the last original variable
    # is the parameter itself. Otherwise all original variables are parametrized.
    coordinate_map={nm:cc[0][1] for nm,cc in zip(order[:-1],coordinates)}
    if order[-1] in face.chart.names:coordinate_map[order[-1]]=[0,1]
    if set(coordinate_map)!=set(face.chart.names):raise ValueError('RUR variable mismatch')
    names=tuple(f'vv{i}' for i in range(face.chart.n))
    src=[f'ring rr={p},(tt),dp;',f'poly ff={univariate_string(eliminant[1])};',
         f'poly dd={univariate_string(denominator[1])};',
         'print("RUR_DEG "+string(deg(ff)));',
         'print("RUR_SQUAREFREE "+string(deg(gcd(ff,diff(ff,tt)))==0));',
         'print("RUR_DENOMINATOR "+string(deg(gcd(ff,dd))==0));',
         'list eg=extgcd(dd,ff); poly dinv=eg[2];',
         'ideal BB=ff; attrib(BB,"isSB",1);']
    for i,nm in enumerate(face.chart.names):
        if nm==order[-1]:
            src.append(f'poly vv{i}=tt;')
        else:
            # msolve stores the relation denominator*x_i + numerator_i=0.
            src.append(f'poly vv{i}=reduce(-({univariate_string(coordinate_map[nm])})*dinv,BB);')
    src+=['int input_ok=1;']
    for f in polys:
        src.append(f'if(reduce(({poly_string(f,names)}),BB)!=0){{input_ok=0;}}')
    src.append('print("RUR_INPUT "+string(input_ok));')
    src.append('poly hh=1;')
    for nm in names:src.append(f'hh=reduce(hh*{nm},BB);')
    src.append('print("RUR_TORUS "+string(deg(gcd(ff,hh))==0));')
    if order[-1] in face.chart.names:
        expr=f'vv{face.chart.names.index(order[-1])}-tt'
    else:
        expr='+'.join(f'{int(linear[i])}*vv{face.chart.names.index(nm)}'
                      for i,nm in enumerate(order[:-1]))+'+tt'
    src.append(f'print("RUR_SEPARATING "+string(reduce(({expr}),BB)==0));')
    src.append('quit;')
    source='\n'.join(src)+'\n'
    temp_root=os.environ.get('NF6_DATA_DIR')
    if temp_root:Path(temp_root).mkdir(parents=True,exist_ok=True)
    started=time.monotonic()
    with tempfile.TemporaryDirectory(prefix='nf6-rur-',dir=temp_root) as tmp:
        path=Path(tmp)/'verify.sing';path.write_text(source)
        proc=subprocess.Popen([shutil.which('Singular') or 'Singular','--no-rc','-q',str(path)],
            stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,
            env=dict(os.environ,OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1'))
        print(json.dumps(dict(stage='rur_Singular_verify',p=p,pid=proc.pid)),flush=True)
        try:
            out,_=proc.communicate(timeout=timeout);timed_out=False
        except subprocess.TimeoutExpired:
            proc.terminate()
            try:out,_=proc.communicate(timeout=5)
            except subprocess.TimeoutExpired:proc.kill();out,_=proc.communicate()
            timed_out=True
    tags=['SQUAREFREE','DENOMINATOR','INPUT','TORUS','SEPARATING']
    checks={tag:bool(re.search(r'RUR_'+tag+r' 1\b',out)) for tag in tags}
    errors=[line for line in out.splitlines() if '?' in line or 'error' in line.lower()]
    passed=all(checks.values()) and not errors and not timed_out and proc.returncode==0
    return dict(status='PASS' if passed else 'TIMEOUT' if timed_out else 'ERROR',
        distinct_torus_points=eliminant[0] if passed else None,reported_degree=degree,
        eliminant_degree=eliminant[0],checks=checks,stdout=out,errors=errors,
        seconds=round(time.monotonic()-started,6),source_sha256=hashlib.sha256(source.encode()).hexdigest())


def leading_monomials(result,names):
    """Read the documented -g output (one polynomial per line)."""
    body=result[result.index('[')+1:result.rindex(']')]
    out=[]
    for poly in body.split(','):
        term=poly.strip().split('+')[0].split('-')[0]
        if not term: raise ValueError('unexpected signed leading term')
        ee=[0]*len(names)
        for nm,exp in re.findall(r'\*([A-Za-z][A-Za-z0-9_]*)\^(\d+)',term):
            ee[names.index(nm)]=int(exp)
        out.append(tuple(ee))
    return out


def staircase_length(lms,n):
    """Count a zero-dimensional monomial quotient by recursive slicing.

    At the last coordinate's exponent k, retain projected monomial generators
    whose last exponent <=k. Every quotient monomial belongs to exactly one
    slice. The pure power bound proves that every slice has been visited.
    """
    from functools import lru_cache
    @lru_cache(None)
    def count(gens,n):
        if any(not any(g) for g in gens):return 0
        if n==0:return 1
        pure=[g[-1] for g in gens if not any(g[:-1])]
        if not pure:raise ValueError('leading ideal not zero-dimensional')
        bound=min(pure)
        result=0
        previous=None
        previous_count=None
        for k in range(bound):
            gg=tuple(sorted(set(g[:-1] for g in gens if g[-1]<=k)))
            if gg==previous:
                value=previous_count
            else:
                value=count(gg,n-1)
            result+=value
            previous=gg;previous_count=value
        return result
    return count(tuple(sorted(set(lms))),n)


def msolve_run(case,p,timeout=600,threads=1,verbose=1,gb=2,saturation=True):
    face=face_at(build_chart(case['d'],case['c'],case['s'],p),case['w'].split(','))
    exact=face_at(build_chart(case['d'],case['c'],case['s']),case['w'].split(','))
    if [set(f) for f in face.forms] != [set(f) for f in exact.forms]:
        raise ValueError('bad prime: exact face support changed')
    names=face.chart.names
    polys=generic_square(face)
    system_source=','.join(names)+'\n'+str(p)+'\n'+',\n'.join(poly_string(f,names) for f in polys)+'\n'
    source=','.join(names)+'\n'+str(p)+'\n'+',\n'.join(
        [poly_string(f,names) for f in polys]+(['*'.join(names)] if saturation else []))+'\n'
    env=dict(os.environ,OMP_NUM_THREADS=str(threads),OPENBLAS_NUM_THREADS='1',VECLIB_MAXIMUM_THREADS='1')
    started=time.monotonic()
    temp_root=os.environ.get('NF6_DATA_DIR')
    if temp_root:Path(temp_root).mkdir(parents=True,exist_ok=True)
    rur_verify=None
    with tempfile.TemporaryDirectory(prefix='nf6-msolve-',dir=temp_root) as tmp:
        inp=Path(tmp)/'input.ms';outp=Path(tmp)/'result.ms'
        inp.write_text(source)
        cmd=[shutil.which('msolve') or 'msolve','-f',str(inp),'-o',str(outp),'-g',str(gb),
             '-t',str(threads),'-v',str(verbose),'-l','2','--random-seed',str(SEED)]
        if saturation:cmd+=['-S']
        proc=subprocess.Popen(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,env=env)
        print(json.dumps(dict(stage='msolve',pid=proc.pid,p=p,source_sha256=hashlib.sha256(source.encode()).hexdigest())),flush=True)
        try:
            out,_=proc.communicate(timeout=timeout);timed_out=False
        except subprocess.TimeoutExpired:
            proc.terminate()
            try:out,_=proc.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill();out,_=proc.communicate()
            timed_out=True
        result=outp.read_text() if outp.exists() else ''
        if not saturation and result and temp_root:
            # Compact certificates can be independently reverified after a code
            # fix without recomputing the expensive original Groebner basis.
            (Path(temp_root)/f'cal_rur_d{case["d"]}_c{case["c"]}_s{case["s"]}_p{p}.txt').write_text(result)
        if saturation and gb==2 and result and not timed_out and proc.returncode==0:
            lms=leading_monomials(result,names)
            length=staircase_length(lms,len(names))
        else:length=None
        if not saturation and gb==0 and result and not timed_out and proc.returncode==0:
            rur_verify=verify_rur(result,face,polys,timeout=timeout)
    return dict(status='TIMEOUT' if timed_out else 'DONE' if proc.returncode==0 else 'ERROR',
        p=p,seed=SEED,seconds=round(time.monotonic()-started,6),returncode=proc.returncode,
        stdout=out,result=result,input_sha256=hashlib.sha256(source.encode()).hexdigest(),
        result_sha256=hashlib.sha256(result.encode()).hexdigest(),threads=threads,
        saturation=saturation,scheme_length_from_leading_ideal=length,rur_verification=rur_verify,
        system_sha256=hashlib.sha256(system_source.encode()).hexdigest(),
        d=case['d'],chart=[case['c'],case['s']],weight=list(map(str,face.w)),
        exact_face_support_preserved=True)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--case',choices=CASES,default='d6_surface1920')
    ap.add_argument('--p',type=int,default=30241)
    ap.add_argument('--timeout',type=float,default=600)
    ap.add_argument('--threads',type=int,default=1,choices=[1,2])
    ap.add_argument('--verbose',type=int,default=1,choices=[0,1,2])
    ap.add_argument('--gb',type=int,default=2,choices=[0,1,2])
    ap.add_argument('--solve',action='store_true',help='ordinary affine solve, without saturation')
    args=ap.parse_args()
    ans=msolve_run(CASES[args.case],args.p,args.timeout,args.threads,args.verbose,args.gb,not args.solve)
    # Keep each line/file below the repository limit.  Full bases, if required,
    # must be handled before this temporary directory closes by the verifier.
    result=ans.pop('result')
    ans['result_bytes']=len(result.encode())
    ans['result_preview']=result[:20000]
    print(json.dumps(ans,sort_keys=True),flush=True)


if __name__=='__main__':main()
