#!/usr/bin/env python3
"""Exact equal-overlap Fourier chart over F_p, with auditable Singular output.

Seed 20261031 (no random choices in this stage).  C_rs = sum_i
a_i b_(i+r) b_(i+s) a_(i+r+s) = t(delta_r0+delta_s0).
Chart a0=b0=1 meets every WH orbit, since t!=0 forces some a_i*b_i!=0.
Usage: python3 e01_fibre.py d p [timeout=900] [lex=1]
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
from pathlib import Path
import platform, resource, subprocess, sys, time

ROOT=Path(__file__).resolve().parents[1]
def program(d,p,lex=True):
    names=['y','t']+[f'b{i}' for i in range(1,d)]+[f'a{i}' for i in range(1,d)]
    av=['1']+[f'a{i}' for i in range(1,d)]
    bv=['1']+[f'b{i}' for i in range(1,d)]
    def prod(xs):
        counts={}
        for x in xs:
            if x!='1': counts[x]=counts.get(x,0)+1
        return '*'.join(x+(f'^{n}' if n>1 else '') for x,n in sorted(counts.items())) or '1'
    forms={}
    for r in range(d):
        for s in range(d):
            terms=sorted(prod([av[i],bv[(i+r)%d],bv[(i+s)%d],av[(i+r+s)%d]]) for i in range(d))
            rhs=int(r==0)+int(s==0)
            form='+'.join(terms)+(f'-{rhs}*t' if rhs else '')
            forms[tuple(terms)+(rhs,)]=form
    n='+'.join(prod([av[i],bv[i]]) for i in range(d))
    code=f'''ring R={p},({','.join(names)}),dp;
short=0; option(redSB);
ideal I={','.join(forms.values())},t*y-1;
poly N={n};
ideal G=std(I);
"FULL_DIM",dim(G); "FULL_LENGTH",vdim(G);
ideal H=std(G+ideal(N));
"NULL_DIM",dim(H); "NULL_LENGTH",vdim(H);
"TRACE_SQUARE_REMAINDER",reduce(N^2-({d+1})*t,G);
"BEGIN_DP"; H; "END_DP";
'''
    if lex:
        code+=f'''ring L={p},({','.join(names)}),lp; short=0;
ideal J=fglm(R,H);
"BEGIN_LEX"; J; "END_LEX";
'''
    return code+'quit;\n'

def main():
    d,p=map(int,sys.argv[1:3]); timeout=int(sys.argv[3]) if len(sys.argv)>3 else 900
    lex=bool(int(sys.argv[4])) if len(sys.argv)>4 else True
    stem=ROOT/'numerics'/f'e01_d{d}_p{p}'
    code=program(d,p,lex); stem.with_suffix('.sing').write_text(code)
    start=time.monotonic()
    print(f'Python {platform.python_version()} d={d} p={p} seed=20261031 exact=Fp timeout={timeout}',flush=True)
    try:
        r=subprocess.run(['Singular','-q'],input=code,text=True,capture_output=True,timeout=timeout)
        stem.with_suffix('.singular.out').write_text(r.stdout+r.stderr)
        print(r.stdout,flush=True); print(r.stderr,flush=True)
        print(f'elapsed={time.monotonic()-start:.3f} returncode={r.returncode}',flush=True)
    except subprocess.TimeoutExpired as e:
        raw=e.stdout or b''
        if isinstance(raw,bytes): raw=raw.decode(errors='replace')
        stem.with_suffix('.singular.out').write_text(raw+'\nTIMEOUT\n')
        print(raw); print(f'TIMEOUT elapsed={time.monotonic()-start:.3f}',flush=True)
if __name__=='__main__': main()
