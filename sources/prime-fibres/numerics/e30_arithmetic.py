#!/usr/bin/env python3
"""Exact discriminants of the SG4a/5a/6a coordinate and overlap fields.

Read-only reuse of already verified exact SG source vectors.  Standard-library
Python and one PARI/GP child at a time.  No Groebner computation, floating-point
recognition, external model, network access, or writes outside this directory.
Run from the repository root:
  python3 .../numerics/e30_arithmetic.py > .../numerics/e30_arithmetic.out

For each proposed primitive element T, exact power-basis rank and membership
of EVERY listed field generator certify Q(T)=Q(generators).  nfdisc computes
the maximal-order field discriminant, not the discriminant of the displayed
primitive polynomial.  The full source tower is first certified to be a field
by an irreducible primitive polynomial of its complete quotient dimension.
All GP children use one thread and a 2 GiB stack maximum, below the 8 GiB cap.
Only owned subprocess PIDs can be terminated by subprocess.run on timeout.
"""
from __future__ import annotations

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
import platform
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = public_root(__file__)
SOURCE = REPO / "sources/d6-seed/numerics"
GP = executable("gp")
SEED = 20261031


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


COMMON = r'''
/* CV is the exact coefficient vector in the full triangular quotient. */
CV(z)={my(A=[liftall(z)]);forstep(h=NV,1,-1,A=concat(vector(#A,k,vector(DG[h],j,polcoef(A[k],j-1,variable(GG[h]))))));if(#A!=FDIM,error("coefficient dimension"));A};
TH=sum(h=1,NV,GG[h]);PSRC=ann(TH);
if(poldegree(PSRC)!=FDIM || !polisirreducible(PSRC),error("source field not certified"));
print("SOURCE_FIELD|",[FDIM,Vec(PSRC),1]);
/* Coefficient, projective ket/bra and matrix-projector field generators. */
PB=vector(d,j,star(PV[j]));
kp=0;for(j=1,d,if(PV[j]!=0,kp=j;break));if(kp==0,error("zero source ket"));
AP=vector(d,j,PV[j]/PV[kp]);BP=vector(d,j,PB[j]/PB[kp]);
PI=matrix(d,d,r,c,PV[r]*PB[c]/NN);
if(trace(PI)!=1 || PI^2!=PI,error("source projector"));
for(r=1,d,for(c=1,d,if(star(PI[r,c])!=PI[c,r],error("Hermiticity"))));
GPI=vector(d^2,j,PI[(j-1)\d+1,(j-1)%d+1]);
/* A diagnostic displacement q=(d/3,2d/3) for 6a.  This SG source is not
   assumed to be the centred representative of the ACFW footnote. */
OSC=if(d==6,vector(d^2,j,my(a=(j-1)\d,b=(j-1)%d);OM^(b*(d/3)-a*(2*d/3))*OV[j]),OV);

/* Certify a field by a primitive element and all-generator membership.
   The candidate is an explicitly recorded integer linear combination. */
field(tag,GS)={my(T,Q,deg,B,GM,ok=0,coeff,P,D,PD,ind2,fac,tries=0);
  GS=Vec(Set(GS));GS=select(z->type(z)!="t_INT" && type(z)!="t_FRAC",GS);
  if(#GS==0,print("FIELD|",tag,"|",[1,[1,0],1,[],1,[],[],0]);return(0));
  for(at=1,12,
    tries=at;coeff=vector(#GS,j,random(19)-9);T=sum(j=1,#GS,coeff[j]*GS[j]);
    if(T==0,next);Q=ann(T);deg=poldegree(Q);
    B=matrix(FDIM,deg);my(vv=1);for(j=1,deg,B[,j]=CV(vv)~;vv*=T);
    GM=matrix(FDIM,#GS,r,c,CV(GS[c])[r]);
    if(matrank(B)==deg && matrank(matconcat([B,GM]))==deg,ok=1;break));
  if(!ok || !polisirreducible(Q),error(Str("primitive membership failed: ",tag)));
  /* polredbest changes the generator, never the number field. */
  P=polredbest(Q);if(!polisirreducible(P) || poldegree(P)!=deg,error("reduced field degree"));
  D=nfdisc(P);PD=poldisc(P);ind2=PD/D;
  if(ind2<=0 || !issquare(ind2),error("field discriminant/index consistency"));
  fac=factor(abs(D));fac=vector(matsize(fac)[1],j,[fac[j,1],fac[j,2]]);
  print("FIELD|",tag,"|",[deg,Vec(P),D,fac,ind2,coeff,Vec(Q),tries]);
  print("FIELD_CERTIFICATE|",tag,"|",[FDIM,#GS,deg,1,1,1]);
  return(P)
};
field("ket_projective",AP);
field("bra_projective",BP);
field("pair_projective",concat(AP,BP));
field("projector",GPI);
field("alpha_native",OV);
field("alpha_displaced_q_n_2n",OSC);
field("E_coordinate_tau",concat(GPI,[TA]));
field("E_overlap_tau",concat(OV,[TA]));
field("cyclotomic_tau",[TA]);

/* Obtain sqrt(d+1) in the source field if possible.  Otherwise extend by a
   proven irreducible quadratic, keeping source-extension distinctions. */
NF=nfinit(PSRC);SQROOTS=nfroots(NF,X^2-(d+1));
if(#SQROOTS,SQ=subst(lift(SQROOTS[1]),Y,TH);SQIN=1,SQ=Mod(ss,ss^2-(d+1));SQIN=0;NV++;DG=concat(DG,[2]);GG=concat(GG,[SQ]);REL=concat(REL,[ss^2-(d+1)]);FDIM*=2);
if(SQ^2!=d+1,error("phase square root"));
print("SQRT_IN_SOURCE|",[d+1,SQIN,FDIM]);
UU=vector(d^2-1,j,SQ*OV[j+1]);USC=vector(d^2-1,j,SQ*OSC[j+1]);
field("u_native",UU);
field("u_displaced_q_n_2n",USC);
field("u_native_tau",concat(UU,[TA]));
field("E_sqrt",concat(concat(GPI,[TA]),[SQ]));

/* Independent class-field discriminant, using the maximal quadratic order.
   bnf certification removes a conditional class-group input. */
DK=core((d+1)*(d-3));BM=bnfinit(Y^2-DK,1);
if(!bnfcertify(BM),error("quadratic bnf not certified"));
DM=if(d%2,d,2*d);BR=bnrinit(BM,[DM,[1,1]],1);
RDISC=bnrdisc(BR);COND=bnrconductor(BR);
FD=factor(abs(RDISC[3]));FD=vector(matsize(FD)[1],j,[FD[j,1],FD[j,2]]);
print("RAY_CLASS_BOTH|",[DK,BM.disc,DM,BR.no,BR.cyc,RDISC,FD,COND[2]]);
for(ii=1,2,my(arch=vector(2,j,j==ii),br=bnrinit(BM,[DM,arch],1),rd=bnrdisc(br),ff=factor(abs(rd[3])));ff=vector(matsize(ff)[1],j,[ff[j,1],ff[j,2]]);print("RAY_CLASS_ONE|",[ii,br.no,br.cyc,rd,ff]));
print("STAGE_COMPLETE|1");quit;
'''


def make_program(rep: str) -> tuple[str, Path]:
    source = SOURCE / f"e01_{rep}.gp"
    prefix = source.read_text().split("/* Exact root-multiple classes")[0]
    if "ann(z)" not in prefix or "PV=vector" not in prefix:
        raise ValueError("source prefix is missing the exact vector or annihilator")
    prefix = prefix.replace("setrand(20261028)", f"setrand({SEED})")
    # X must have higher priority than Y, and ss higher than every tower var.
    priority = "[X,Y,ss," + ",".join(f"t{j}" for j in reversed(range(5 if rep != "4a" else 4))) + "];"
    old = "[Y," + ",".join(f"t{j}" for j in reversed(range(5 if rep != "4a" else 4))) + "];"
    if old not in prefix:
        raise ValueError("unexpected source variable order")
    prefix = prefix.replace(old, priority)
    prefix = prefix.replace("default(parisizemax,1073741824)", "default(parisizemax,2147483648)")
    return prefix + COMMON, source


def parse_rows(output: str) -> list[dict]:
    rows = []
    for line in output.splitlines():
        if "|" not in line:
            continue
        parts = line.split("|")
        try:
            payload = json.loads(parts[-1])
        except json.JSONDecodeError:
            payload = parts[-1]
        rows.append({"kind": parts[0], "tag": parts[1] if len(parts) == 3 else None,
                     "value": payload})
    return rows


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--rep", nargs="+", default=["4a", "5a", "6a"])
    ap.add_argument("--timeout", type=int, default=600)
    args = ap.parse_args()
    result = {"schema": "sic-arithmetic-v1", "seed": SEED, "threads": 1,
              "python": sys.version, "platform": platform.platform(),
              "arithmetic": "exact rational/PARI maximal-order discriminants",
              "memory_stack_max_bytes": 2147483648,
              "script_sha256": sha(Path(__file__)), "representatives": [],
              "status": "ERROR"}
    env = dict(os.environ, OMP_NUM_THREADS="1", OPENBLAS_NUM_THREADS="1",
               MKL_NUM_THREADS="1", VECLIB_MAXIMUM_THREADS="1")
    for rep in args.rep:
        program, source = make_program(rep)
        start = time.monotonic()
        run = subprocess.run([GP, "-fq", "-s", "134217728"], input=program,
                             text=True, capture_output=True, timeout=args.timeout, env=env)
        stderr = "\n".join(line for line in run.stderr.splitlines()
                           if line.strip() and "Warning: new maximum stack size" not in line
                           and "Warning: increasing stack size" not in line)
        row = {"rep": rep, "source": str(source.relative_to(REPO)),
               "source_sha256": sha(source),
               "gp_program_sha256": hashlib.sha256(program.encode()).hexdigest(),
               "command": [GP, "-fq", "-s", "134217728"],
               "seconds": round(time.monotonic() - start, 3),
               "returncode": run.returncode, "stderr": stderr,
               "rows": parse_rows(run.stdout)}
        result["representatives"].append(row)
        if run.returncode or stderr or "STAGE_COMPLETE|1" not in run.stdout:
            row["raw_stdout"] = run.stdout
            print(json.dumps(result, ensure_ascii=False, indent=2))
            raise SystemExit(1)
    result["status"] = "CERTIFIED"
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
