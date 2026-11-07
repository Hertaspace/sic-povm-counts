#!/usr/bin/env python3.14
"""Read-only bounded audit of e10's component certificate. No CAS subprocess.

Independent AST parser and sparse F7[w]/(w^2+1) arithmetic replay members.
Upstream generator code is imported read-only to compare the declared input.
Only e90_component_audit.json and redirected e90 stdout are written.
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
import ast, gzip, hashlib, json, signal, time
from fractions import Fraction
from pathlib import Path
signal.alarm(60)
H = Path(__file__).resolve().parent
START = time.monotonic()
ZERO, ONE = (0, 0), (1, 0)

def ca(a, b):
    return ((a[0]+b[0]) % 7, (a[1]+b[1]) % 7)
def cm(a, b):
    return ((a[0]*b[0]-a[1]*b[1]) % 7, (a[0]*b[1]+a[1]*b[0]) % 7)
def cn(a):
    return (-a[0] % 7, -a[1] % 7)
def cp(a, n):
    n %= 48
    b = ONE
    while n:
        if n & 1: b = cm(b, a)
        a = cm(a, a)
        n //= 2
    return b
def sc(c):
    return {} if c == ZERO else {(): c}
def add(a, b):
    out = dict(a)
    for m, c in b.items():
        out[m] = ca(out.get(m, ZERO), c)
        if out[m] == ZERO: del out[m]
    return out
def neg(a):
    return {m: cn(c) for m, c in a.items()}
def mul(a, b):
    out = {}
    for m, c in a.items():
        for n, d in b.items():
            key = tuple(sorted(m+n))
            out[key] = ca(out.get(key, ZERO), cm(c, d))
            if out[key] == ZERO: del out[key]
    return out
def power(a, n):
    assert n >= 0
    b = sc(ONE)
    while n:
        if n & 1: b = mul(b, a)
        a = mul(a, a)
        n //= 2
    return b
def parse(s):
    def visit(n):
        if isinstance(n, ast.Constant):
            assert isinstance(n.value, int)
            return sc((n.value % 7, 0))
        if isinstance(n, ast.Name):
            if n.id == "w": return sc((0, 1))
            assert n.id in ("t", "y") or (n.id.startswith("z") and n.id[1:].isdigit())
            return {(n.id,): ONE}
        if isinstance(n, ast.UnaryOp):
            a = visit(n.operand)
            if isinstance(n.op, ast.USub): return neg(a)
            assert isinstance(n.op, ast.UAdd)
            return a
        assert isinstance(n, ast.BinOp)
        if isinstance(n.op, ast.Pow):
            assert isinstance(n.right, ast.Constant)
            return power(visit(n.left), n.right.value)
        a, b = visit(n.left), visit(n.right)
        if isinstance(n.op, ast.Add): return add(a, b)
        if isinstance(n.op, ast.Sub): return add(a, neg(b))
        assert isinstance(n.op, ast.Mult)
        return mul(a, b)
    return visit(ast.parse(s.replace("^", "**"), mode="eval").body)

def unpack(m):
    raw = gzip.decompress(b"".join((H/f).read_bytes() for f in m["files"]))
    assert hashlib.sha256(raw).hexdigest() == m["uncompressed_sha256"]
    return raw

summary = json.loads((H/"e10_p7_component.json").read_text())
cut = json.loads(unpack(summary["certificate"]))
assert cut["d"] == 6 and cut["p"] == 7 and cut["mask"] == 1056968640
assert cut["first_label"] == 6 and cut["fixed_minimal_residue_point"] is False
assert cut["residue_component_normalization"]["a_support"] == [0, 3]
assert cut["residue_component_normalization"]["b_support"] == [2, 5]

# This import constructs no child process and writes no file.
import e10_p7 as W
p = W.problem(cut["mask"], component=True)
weights = list(map(Fraction, cut["weights"]))
gens = p.gens(weights)
assert len(gens) == summary["original_count"] == 289
assert p.extra[-8:] == W.COMPONENT_RELATIONS
assert cut["residue_component_normalization"]["relations"] == W.COMPONENT_RELATIONS

total = {}
member_terms = 0
used = set()
for item in cut["members"]:
    i = item["generator_index_zero_based"]
    assert gens[i] == item["generator"]
    f, u = parse(item["generator"]), parse(item["multiplier"])
    member_terms += len(u)
    total = add(total, mul(u, f))
    used.add(i)
assert total == sc(ONE)

# Independent reconstruction of minimal-term indices, not p.describe().
actual = []
for i in sorted({p.mapping[i] for i in used if i < len(p.mapping)}):
    ts = p.cached[i]
    values = [Fraction(v)+sum(weights[q] for q in mon) for mon, v, c in ts]
    low = min(values)
    actual.append(dict(polynomial_index_zero_based=i,
                       leader_term_indices_zero_based=[j for j, v in enumerate(values) if v == low]))
assert actual == cut["cell"]
assert cut["group_images"] == [[s, c] for s in (1, -1) for c in range(6)]

# Independent symbolic reconstruction of the entire residue block.
tau = (0, 3)
assert cp(tau, 6) == (6, 0) and cp(tau, 12) == ONE
z = [{} for _ in range(36)]
z[6] = sc(ONE)
for q in (7, 24, 25): z[q] = parse("z"+str(q))
for q, base, exponent in ((8,6,2),(10,6,4),(9,7,2),(11,7,4),
                          (26,24,8),(28,24,4),(27,25,8),(29,25,4)):
    z[q] = mul(sc(cp(tau, exponent)), z[base])
matrix = {}
for i in range(6):
    for j in range(6):
        r = (i-j) % 6
        entry = {}
        for k in range(6):
            entry = add(entry, mul(sc(cp(tau, r*k+2*k*j)), z[6*r+k]))
        if entry: matrix[i, j] = entry
assert set(matrix) == {(0,2),(0,5),(3,2),(3,5)}
conic = parse("3*z7^2+z24^2+3*z25^2-1")
det = add(mul(matrix[0,2],matrix[3,5]), neg(mul(matrix[0,5],matrix[3,2])))
assert det == mul(sc((2,0)), conic)

# All 12 label symmetries have actual block-preserving representatives.
for sign in (1, -1):
    for c in range(6):
        support = set()
        for (i,j), value in matrix.items():
            ii,jj = (i,j) if sign == 1 else ((-j-1)%6,(-i-1)%6)
            assert mul(sc(cp(tau,c*(ii*ii-jj*jj))),value)
            support.add((ii,jj))
        assert support == set(matrix)
        for r in range(6):
            for k in range(6):
                target = (sign*k+c*r)%6
                ratios = set()
                for j in range(6):
                    i = (j+r)%6
                    if sign == 1:
                        source = cp(tau,r*k+2*k*j)
                    else:
                        source_j = (-i-1)%6
                        source = cp(tau,r*k+2*k*source_j)
                    transformed = cm(cp(tau,c*(i*i-j*j)),source)
                    expected = cp(tau,r*target+2*target*j)
                    ratios.add(cm(transformed,cp(expected,-1)))
                assert len(ratios) == 1 and ZERO not in ratios

# Grade checks include the actual residue coefficient ring (all grade zero).
grade = summary["grading"]
for i, g in enumerate(gens):
    degrees = {sum(grade[x] for x in mon) for mon in parse(g)}
    assert len(degrees) <= 1
    assert not degrees or next(iter(degrees)) == summary["homogeneous_degrees"][i]
assert grade["z6"] == 0 and grade["t"] == 2 and grade["y"] == -2

# Optional bounded SMT replay of the regenerated same necessary system and cut.
# No GB or CAS subprocess is used. Existing certified priors remain explicit.
p.add_orbit(cut["cell"])
p.solver.set(timeout=5000)
smt = str(p.solver.check())
assert smt == "unsat", smt

out = dict(status="PASS",seed=20261031,arithmetic="independent AST and sparse exact F7[w]/(w^2+1)",
    certificate_sha256=summary["certificate"]["uncompressed_sha256"],
    members=len(cut["members"]),multiplier_monomials=member_terms,
    exact_identity="1",declared_generators_match=True,cell_recomputed_from_original_weights=True,
    used_dynamic_initial_polynomials=len(actual),used_extra_indices=sorted(i for i in used if i>=len(p.mapping)),
    block_relations=8,block_parameters=["z7","z24","z25"],
    block_determinant="2*(3*z7^2+z24^2+3*z25^2-1)",
    actual_group_representatives_verified=12,all_289_generators_grade_checked=True,
    regenerated_smt=smt,constructor_prior_files=p.stats["prior_cut_files"],
    explicit_e08c_prior_files=[f.name for f in sorted(W.OLD.glob("e08c_d6_p7_m1056968640_*c[0-9][0-9][0-9].json"))],
    seconds=round(time.monotonic()-START,6),source_sha256={})
for path in (Path(__file__),H/"e10_p7.py",W.OLD/"e08c_cover.py",W.OLD/"e05_initial_forms.py"):
    out["source_sha256"][str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
(H/"e90_component_audit.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out,indent=2))
