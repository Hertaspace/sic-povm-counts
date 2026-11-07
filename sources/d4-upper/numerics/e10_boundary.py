#!/usr/bin/env python3
"""Exact small-dimensional t=0 boundary calculation, one Singular process.

Seed 20261031. ACFW D_(u,v)=tau^(uv) X^u Z^v, using signed -p.
This is the naive projective boundary with Z0^2=0. It is NOT the
horizontal closure of the t!=0 generic fibre. Both the full boundary
and its additional trace-zero quotient are computed on coordinate charts.
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
import argparse
import os
import re
import resource
import subprocess
import sys
import time

parser = argparse.ArgumentParser()
parser.add_argument("--dimension", type=int, default=4)
parser.add_argument("--characteristic", type=int, default=5)
parser.add_argument("--timeout", type=int, default=120)
parser.add_argument("--all-charts", action="store_true")
parser.add_argument("--cells", action="store_true")
args = parser.parse_args()
d = args.dimension
base = Path(__file__).resolve().parent
stem = f"e10_d{d}_p{args.characteristic}"
if args.characteristic == 0:
    field = "(0,w)"
    minpoly = "minpoly=w^4+1;\n"
    assert d == 4
    tau = "w"
elif d == 4 and args.characteristic == 5:
    field = "(25,w)"
    minpoly = ""
    tau = "w^3"
elif d == 5 and args.characteristic == 3:
    field = "(81,w)"
    minpoly = ""
    tau = "w^16"
else:
    raise ValueError("Calibrated cases are d4/p5, d4/p0, d5/p3")

vars_ = [f"a{i}" for i in range(d)] + [f"b{i}" for i in range(d)]
tord = d if d % 2 else 2 * d
body = [f"ring r={field},({','.join(vars_)}),dp;\n", minpoly,
        f"number tau={tau};\n", "option(redSB);\n"]
body.append(f"""
proc T(int e) {{
  e=e mod {tord}; if(e<0) {{e=e+{tord};}}
  return(tau^e);
}}
proc Zf(int u,int v) {{
  poly z=0; int s; int j;
  for(s=0;s<{d};s++) {{
    j=(s+u) mod {d}; if(j<0) {{j=j+{d};}}
    z=z+T(u*v+2*v*s)*var(s+1)*var({d}+j+1);
  }}
  return(z);
}}
proc SF(ideal H) {{
  ideal E=finduni(H); int i; poly f;
  for(i=1;i<=ncols(E);i++) {{
    f=E[i];
    if(deg(f)>0) {{ if(deg(gcd(f,diff(f,var(i))))>0) {{return(0);}} }}
  }}
  return(1);
}}
proc PowerNF(poly f,int n,ideal H) {{
  poly g=1;
  while(n>0) {{
    if(n mod 2==1) {{g=reduce(g*f,H);}}
    n=n div 2;
    if(n>0) {{f=reduce(f*f,H);}}
  }}
  return(g);
}}
""")
q = 25 if args.characteristic == 5 else 81
if args.characteristic:
    radical_step = f"""
    g=gcd(f,var(i)^{q}-var(i));
    if(PowerNF(g,vdim(J),std(ideal(f)))!=0) {{split=0;}}
"""
else:
    radical_step = "g=f/gcd(f,diff(f,var(i)));\n"
body.append(f"""
proc RadicalData(ideal J) {{
  ideal E=finduni(J); ideal U=0; int i; poly f; poly g; int split=1;
  for(i=1;i<=ncols(E);i++) {{
    f=E[i];
    if(deg(f)>0) {{
      {radical_step}
      U=U+ideal(g);
    }}
  }}
  ideal R=std(J+U);
  list result=R,split;
  return(result);
}}
""")
seen = set()
equations = ["Zf(0,0)^2"]
for u in range(d):
    for v in range(d):
        if (u, v) == (0, 0) or (u, v) in seen:
            continue
        seen.add((u, v))
        seen.add((-u % d, -v % d))
        equations.append(f"Zf({u},{v})*Zf({-u},{-v})")
body.append("ideal I=" + ",".join(equations) + ";\n")
body.append('"SINGULAR_VERSION:",system("version");\n')
body.append(f'"ACFW_PHASE_ORDER:",{tord},tau^{tord},tau^{tord//2};\n')
a_charts = range(d) if args.all_charts else [0]
for i in a_charts:
    for j in range(d):
        reduced_cell_ideal = ",".join(
            [f"a{k}" for k in range(i)] + [f"b{k}" for k in range(j)] + ["0"])
        reduced_cell_code = (f'ideal RC=std(R+ideal({reduced_cell_ideal}));\n'
                             f'"REDUCED_CELL {i} {j} LENGTH:",vdim(RC);\nkill RC;\n'
                             if args.cells else "")
        body.append(f"""
ideal C=I+ideal(a{i}-1,b{j}-1);
ideal H=std(C);
int dh=dim(H); int lh=vdim(H);
"FULL_CHART {i} {j} DIM_LENGTH:",dh,lh;
ideal J=std(H+ideal(Zf(0,0)));
int dj=dim(J); int lj=vdim(J);
"TRACE_CHART {i} {j} DIM_LENGTH:",dj,lj;
if(dj==0 && lj>0) {{
  list RD=RadicalData(J); ideal R=RD[1];
  "REDUCED_CHART {i} {j} LENGTH_ALLROOTS:",vdim(R),RD[2];
  "REDUCED_CHART {i} {j} SEPARABLE:",SF(R);
  {reduced_cell_code}
  kill RD,R;
}}
""")
        if args.cells:
            body.append(f"""
if(dh==0 && lh>0) {{
  // In an Artin algebra of length lh, all local nilpotents have exponent <=lh.
  // These powers retain whole primary components where earlier coordinates
  // have zero residue, giving a disjoint count without discarding nilpotents.
  ideal P=0;
""")
            for previous in range(i):
                body.append(f"P=P+ideal(PowerNF(a{previous},lh,H));\n")
            for previous in range(j):
                body.append(f"P=P+ideal(PowerNF(b{previous},lh,H));\n")
            body.append(f"""
  "FULL_CELL {i} {j} LENGTH:",vdim(std(H+P));
  "TRACE_CELL {i} {j} LENGTH:",vdim(std(J+P));
  kill P;
}}
""")
        body.append("""
kill C,H,J,dh,lh,dj,lj;
""")
body.append("quit;\n")
source = "".join(body)
(base / f"{stem}.sing").write_text(source)

environment = os.environ.copy()
environment["OMP_NUM_THREADS"] = "1"
start = time.monotonic()
print(f"CASE d={d} p={args.characteristic} seed=20261031 all_charts={args.all_charts}", flush=True)
singular_command = [executable("Singular"), "--no-rc",
                    "--random=20261031", "--cpus=1", "--threads=1",
                    "--flint-threads=1", "-q"]
print("COMMAND=" + " ".join(singular_command), flush=True)
child = subprocess.Popen(singular_command, stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                         text=True, env=environment)
exit_status = 0
try:
    stdout, stderr = child.communicate(input=source, timeout=args.timeout)
    output = stdout + stderr
    print(output, end="")
    metadata = f"EXIT={child.returncode} ELAPSED={time.monotonic()-start:.3f}\n"
    if args.cells:
        for label in ("FULL", "TRACE", "REDUCED"):
            values = [int(v) for v in re.findall(label+r"_CELL \d+ \d+ LENGTH: (\d+)", output)]
            metadata += f"SUM_{label}_CELLS={sum(values)} COUNTED_CELLS={len(values)}\n"
    print(metadata, end="")
    if child.returncode != 0 or any(line.lstrip().startswith("?") for line in output.splitlines()):
        exit_status = 1
except subprocess.TimeoutExpired as exc:
    child.kill()  # Only the exact child PID launched above.
    stdout, stderr = child.communicate()
    output = stdout + stderr + "\nTIMEOUT\n"
    print(output)
    metadata = f"EXIT=TIMEOUT ELAPSED={time.monotonic()-start:.3f}\n"
    exit_status = 124
finally:
    peak = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    print(f"CHILDREN_RU_MAXRSS_RAW={peak}")
metadata += f"CHILDREN_RU_MAXRSS_RAW={peak}\n"
header = (f"CASE d={d} p={args.characteristic} seed=20261031 all_charts={args.all_charts} cells={args.cells}\n"
          + "COMMAND=" + " ".join(singular_command) + "\n")
(base / f"{stem}.out").write_text(header + output + metadata)
with (base / "e10_boundary.out").open("a") as combined:
    combined.write(header + output + metadata)
sys.exit(exit_status)
