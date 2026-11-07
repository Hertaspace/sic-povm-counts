"""Exact independent F49 polynomial arithmetic shared by e90 audit scripts."""

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
import ast
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

