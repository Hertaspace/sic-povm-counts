#!/usr/bin/env python3.14
"""Audit three new R1 members and replay pure old78+new3 coverage.
No Singular, GB, lift, or e31 import. Writes only e90_r1_plain_audit.json.
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
import sys
sys.dont_write_bytecode = True
sys.setrecursionlimit(20000)
import gzip,hashlib,json,signal,time
from fractions import Fraction
from pathlib import Path
import z3
from e90_exact_arithmetic import parse,add,mul,sc,ONE
H=Path(__file__).resolve().parent
START=time.monotonic()
signal.alarm(60)
import e10_p7 as W

def unpack(root,manifest):
    raw=gzip.decompress(b"".join((root/f).read_bytes() for f in manifest["files"]))
    assert hashlib.sha256(raw).hexdigest()==manifest["uncompressed_sha256"]
    return raw

plain=json.loads((H/"e10_p7_r1_plain.json").read_text())
assert plain["uses_e31_strengthening"] is False
prior=json.loads((W.OLD/"e08c_r1_cli.json").read_text())["source_manifest"]
assert plain["prior_final_smt"]==prior
raw=unpack(W.OLD,prior)
p=W.problem(4032,prior=False)
p.solver=z3.Solver()
p.solver.from_string(raw.decode())
prior_assertions=len(p.solver.assertions())
rows=[]
for manifest in plain["certificates"]:
    cut=json.loads(unpack(H,manifest))
    assert cut["mask"]==4032 and cut["d"]==6 and cut["p"]==7
    assert cut["first_label"]==6 and cut["fixed_minimal_residue_point"] is True
    assert "residue_component_normalization" not in cut
    weights=list(map(Fraction,cut["weights"]))
    gens=p.gens(weights)
    total={}
    used=set()
    for item in cut["members"]:
        i=item["generator_index_zero_based"]
        assert gens[i]==item["generator"]
        total=add(total,mul(parse(item["generator"]),parse(item["multiplier"])))
        used.add(i)
    assert total==sc(ONE)
    cell=[]
    for i in sorted({p.mapping[i] for i in used if i<len(p.mapping)}):
        values=[Fraction(v)+sum(weights[q] for q in mon) for mon,v,c in p.cached[i]]
        low=min(values)
        cell.append(dict(polynomial_index_zero_based=i,
                         leader_term_indices_zero_based=[j for j,v in enumerate(values) if v==low]))
    assert cell==cut["cell"]
    assert cut["group_images"]==[[s,c] for s in (1,-1) for c in range(6)]
    p.add_orbit(cell)
    rows.append(dict(sha256=manifest["uncompressed_sha256"],members=len(used),
                     initial_polynomials=len(cell),identity="1",leaders_rebuilt=True))
assert len(rows)==3
assert len(p.solver.assertions())==prior_assertions+36

# Check the stored pure final SMT is precisely the rebuilt prior plus36 cuts.
saved=z3.Solver()
saved.from_string(unpack(H,plain["final_smt"]).decode())
aa,bb=p.solver.assertions(),saved.assertions()
assert len(aa)==len(bb)
changed=[]
for i,(a,b) in enumerate(zip(aa,bb)):
    if a.eq(b): continue
    # SMT-LIB serialization expands Z3's internal rational multiplication
    # notation. Compare the exact simplified Boolean equality as well.
    equivalent=z3.simplify(a==b,arith_lhs=True,sort_sums=True)
    assert z3.is_true(equivalent),(i,a.sexpr()[:1500],b.sexpr()[:1500],equivalent.sexpr()[:1500])
    changed.append(i)

p.solver.set(timeout=20000)
tick=time.monotonic()
answer=str(p.solver.check())
assert answer=="unsat",answer
out=dict(status="PASS",seed=20261031,uses_e31_strengthening=False,
    old_smt_sha256=prior["uncompressed_sha256"],prior_assertions=prior_assertions,
    new_assertions=36,three_certificates=rows,
    declared_pure_final_smt_exact_assertions_match=True,
    serialization_normalized_assertions=changed,
    regenerated_final_result=answer,check_seconds=round(time.monotonic()-tick,6),
    arithmetic="independent AST and exact sparse F49",seconds=round(time.monotonic()-START,6),
    versions=dict(python=sys.version,z3=z3.get_version_string()),source_sha256={})
for path in (Path(__file__),H/"e90_exact_arithmetic.py",H/"e10_p7.py",W.OLD/"e08c_cover.py",W.OLD/"e05_initial_forms.py"):
    out["source_sha256"][str(path)]=hashlib.sha256(path.read_bytes()).hexdigest()
(H/"e90_r1_plain_audit.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out,indent=2))
