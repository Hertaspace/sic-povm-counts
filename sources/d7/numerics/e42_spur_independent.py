#!/usr/bin/env python3
"""Independent, integer-only replay of spurious-root certificates.

No flint, Arb, NumPy, mpmath, SymPy, or generator code is imported.  Each real
interval endpoint is an integer times 2**(-bits); every inexact arithmetic
operation rounds outwards by integer floor/ceiling division.  The certificate
supplies only exact dyadics, not trusted residual/error estimates.

Public API: FixedContext, ComplexBox, SpurSystem.  Boxes are tuples
(real_lower, real_upper, imag_lower, imag_upper), with the context's common
scale.  evaluate_q builds the original, unscaled signed-pair equations directly
from a and b.  It does not import the symbolic coefficient-table implementation.
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
import gzip
import hashlib
import json
import multiprocessing
from pathlib import Path
import platform
import sys
import time
from typing import NamedTuple

sys.dont_write_bytecode = True


class ComplexBox(NamedTuple):
    rlo: int
    rhi: int
    ilo: int
    ihi: int


def ceildiv(a: int, b: int) -> int:
    return -((-a) // b)


class FixedContext:
    """Outward real intervals and complex rectangles on one dyadic grid."""

    def __init__(self, bits: int = 384):
        if bits < 64:
            raise ValueError("precision must be at least 64 bits")
        self.bits = bits
        self.S = 1 << bits
        self.zero = ComplexBox(0, 0, 0, 0)
        self.one = ComplexBox(self.S, self.S, 0, 0)

    def integer(self, n: int) -> ComplexBox:
        x = int(n) << self.bits
        return ComplexBox(x, x, 0, 0)

    def _dyadic_real(self, numerator: int, exponent: int) -> tuple[int, int]:
        shift = self.bits + int(exponent)
        n = int(numerator)
        if shift >= 0:
            value = n << shift
            return value, value
        denominator = 1 << -shift
        return n // denominator, ceildiv(n, denominator)

    def dyadic(self, real: int, imag: int = 0, scale: int = 0) -> ComplexBox:
        rl, rh = self._dyadic_real(real, scale)
        il, ih = self._dyadic_real(imag, scale)
        return ComplexBox(rl, rh, il, ih)

    def rect(self, real, imag, scale: int) -> ComplexBox:
        rl, _ = self._dyadic_real(real[0], scale)
        _, rh = self._dyadic_real(real[1], scale)
        il, _ = self._dyadic_real(imag[0], scale)
        _, ih = self._dyadic_real(imag[1], scale)
        if rl > rh or il > ih:
            raise ValueError("reversed rectangle")
        return ComplexBox(rl, rh, il, ih)

    def add(self, z, w) -> ComplexBox:
        return ComplexBox(z[0]+w[0], z[1]+w[1], z[2]+w[2], z[3]+w[3])

    def neg(self, z) -> ComplexBox:
        return ComplexBox(-z[1], -z[0], -z[3], -z[2])

    def sub(self, z, w) -> ComplexBox:
        return ComplexBox(z[0]-w[1], z[1]-w[0], z[2]-w[3], z[3]-w[2])

    def conj(self, z) -> ComplexBox:
        return ComplexBox(z[0], z[1], -z[3], -z[2])

    def _real_mul(self, al: int, ah: int, bl: int, bh: int):
        S = self.S
        if al == ah:
            if al >= 0:
                return al*bl // S, ceildiv(al*bh, S)
            return al*bh // S, ceildiv(al*bl, S)
        if bl == bh:
            if bl >= 0:
                return bl*al // S, ceildiv(bl*ah, S)
            return bl*ah // S, ceildiv(bl*al, S)
        if al >= 0:
            if bl >= 0:
                return al*bl // S, ceildiv(ah*bh, S)
            if bh <= 0:
                return ah*bl // S, ceildiv(al*bh, S)
            return ah*bl // S, ceildiv(ah*bh, S)
        if ah <= 0:
            if bl >= 0:
                return al*bh // S, ceildiv(ah*bl, S)
            if bh <= 0:
                return ah*bh // S, ceildiv(al*bl, S)
            return al*bh // S, ceildiv(al*bl, S)
        if bl >= 0:
            return al*bh // S, ceildiv(ah*bh, S)
        if bh <= 0:
            return ah*bl // S, ceildiv(al*bl, S)
        products = (al*bl, al*bh, ah*bl, ah*bh)
        return min(products) // S, ceildiv(max(products), S)

    def mul(self, z, w) -> ComplexBox:
        ac = self._real_mul(z[0], z[1], w[0], w[1])
        bd = self._real_mul(z[2], z[3], w[2], w[3])
        ad = self._real_mul(z[0], z[1], w[2], w[3])
        bc = self._real_mul(z[2], z[3], w[0], w[1])
        return ComplexBox(ac[0]-bd[1], ac[1]-bd[0], ad[0]+bc[0], ad[1]+bc[1])

    def mul_int(self, z, n: int) -> ComplexBox:
        n = int(n)
        if n >= 0:
            return ComplexBox(*(x*n for x in z))
        return ComplexBox(z[1]*n, z[0]*n, z[3]*n, z[2]*n)

    def div_int(self, z, n: int) -> ComplexBox:
        n = int(n)
        if n == 0:
            raise ZeroDivisionError
        if n < 0:
            return self.div_int(self.neg(z), -n)
        return ComplexBox(z[0]//n, ceildiv(z[1],n), z[2]//n, ceildiv(z[3],n))

    def _real_square(self, lo: int, hi: int):
        if lo >= 0:
            return lo*lo // self.S, ceildiv(hi*hi, self.S)
        if hi <= 0:
            return hi*hi // self.S, ceildiv(lo*lo, self.S)
        return 0, ceildiv(max(lo*lo,hi*hi), self.S)

    def div(self, z, w) -> ComplexBox:
        """Complex division; reject whenever zero cannot be excluded."""
        rr = self._real_square(w[0], w[1])
        ii = self._real_square(w[2], w[3])
        lower, upper = rr[0]+ii[0], rr[1]+ii[1]
        if lower <= 0:
            raise ZeroDivisionError("complex denominator may contain zero")
        num = self.mul(z, self.conj(w))
        def real_div(lo, hi):
            values = (lo*self.S//lower, lo*self.S//upper,
                      hi*self.S//lower, hi*self.S//upper)
            uppers = (ceildiv(lo*self.S,lower), ceildiv(lo*self.S,upper),
                      ceildiv(hi*self.S,lower), ceildiv(hi*self.S,upper))
            return min(values), max(uppers)
        re = real_div(num[0], num[1])
        im = real_div(num[2], num[3])
        return ComplexBox(*re, *im)

    def inflate(self, z, radius: int) -> ComplexBox:
        if radius < 0:
            raise ValueError("negative radius")
        return ComplexBox(z[0]-radius,z[1]+radius,z[2]-radius,z[3]+radius)

    def midpoint(self, z) -> ComplexBox:
        re, im = (z[0]+z[1])//2, (z[2]+z[3])//2
        return ComplexBox(re,re,im,im)

    @staticmethod
    def exact(z) -> bool:
        return z[0] == z[1] and z[2] == z[3]

    @staticmethod
    def excludes_zero(z) -> bool:
        return z[0] > 0 or z[1] < 0 or z[2] > 0 or z[3] < 0

    @staticmethod
    def abs1_upper(z) -> int:
        return max(abs(z[0]),abs(z[1])) + max(abs(z[2]),abs(z[3]))

    @staticmethod
    def contains(z, w) -> bool:
        return z[0] <= w[0] <= w[1] <= z[1] and z[2] <= w[2] <= w[3] <= z[3]

    @staticmethod
    def interior_contains(z, w) -> bool:
        return z[0] < w[0] <= w[1] < z[1] and z[2] < w[2] <= w[3] < z[3]

    def sum(self, boxes) -> ComplexBox:
        rr = [0,0,0,0]
        for z in boxes:
            rr[0]+=z[0]; rr[1]+=z[1]; rr[2]+=z[2]; rr[3]+=z[3]
        return ComplexBox(*rr)

    def encode(self, z) -> dict:
        return {"scale":-self.bits,"real":[str(z[0]),str(z[1])],
                "imag":[str(z[2]),str(z[3])]}


def polynomial(ctx, coefficients, z):
    out = ctx.zero
    for c in reversed(coefficients):
        out = ctx.add(ctx.mul(out,z),ctx.integer(c))
    return out


def certify_omega(ctx: FixedContext, d: int, omega: ComplexBox) -> dict:
    """Authenticate the supplied coefficient enclosure without transcendents.

    Phi_6=z^2-z+1 and Phi_7=1+...+z^6.  Exact complex Krawczyk inclusion
    proves a unique root in the supplied rectangle, with a strict contraction.
    Im>0 (d=6), respectively Re>0 and Im>0 (d=7), selects exp(2*pi*i/d)
    among the roots of the relevant cyclotomic polynomial.
    """
    coeffs = {6:[1,-1,1], 7:[1,1,1,1,1,1,1]}.get(d)
    if coeffs is None:
        raise ValueError("only authenticated d=6 and d=7 are supported")
    if omega[2] <= 0 or (d == 7 and omega[0] <= 0):
        raise ValueError("omega does not lie in the selecting quadrant")
    c = ctx.midpoint(omega)
    deriv = [k*coeffs[k] for k in range(1,len(coeffs))]
    dc = ctx.midpoint(polynomial(ctx,deriv,c))
    dr, di = dc[0], dc[2]
    denom = dr*dr+di*di
    if not denom:
        raise ValueError("zero midpoint cyclotomic derivative")
    ar = dr*ctx.S*ctx.S//denom
    ai = -di*ctx.S*ctx.S//denom
    A = ComplexBox(ar,ar,ai,ai)
    defect = ctx.sub(ctx.one,ctx.mul(A,polynomial(ctx,deriv,omega)))
    eta = ctx.abs1_upper(defect)
    if eta >= ctx.S:
        raise ValueError("omega contraction failed")
    image = ctx.add(ctx.sub(c,ctx.mul(A,polynomial(ctx,coeffs,c))),
                    ctx.mul(defect,ctx.sub(omega,c)))
    if not ctx.interior_contains(omega,image):
        raise ValueError("omega strict Krawczyk inclusion failed")
    return {"passed":True,"polynomial":coeffs,"selection":"Im>0" if d==6 else "Re>0, Im>0",
            "eta_upper":str(eta),"scale":-ctx.bits,"image":ctx.encode(image)}


def _matrix_from_header(header, ctx):
    M = header["M"]
    if "rows" in M:
        return [[ctx.dyadic(*entry,scale=int(M["scale"])) for entry in row] for row in M["rows"]]
    re, im = M["real_numerators"], M["imag_numerators"]
    denominator = int(M.get("denominator",4294967296))
    if denominator <= 0 or denominator & (denominator-1):
        raise ValueError("matrix denominator must be a power of two")
    scale = -(denominator.bit_length()-1)
    return [[ctx.dyadic(r,i,scale) for r,i in zip(rrow,irow)] for rrow,irow in zip(re,im)]


def verify_matrix_binding(header, base_dir=None):
    """Bind the normalized certificate M to the immutable raw e40 matrix."""
    if "matrix_file" not in header and "matrix_sha256" not in header:
        return None
    if "matrix_file" not in header or "matrix_sha256" not in header:
        raise ValueError("incomplete original matrix binding")
    name=Path(header["matrix_file"])
    candidates=[name,Path(__file__).parent/name]
    if base_dir is not None:
        candidates.insert(0,Path(base_dir)/name)
    path=next((p for p in candidates if p.is_file()),None)
    if path is None:
        raise FileNotFoundError(f"original matrix file required: {name}")
    data=path.read_bytes()
    digest=hashlib.sha256(data).hexdigest()
    if digest!=header["matrix_sha256"]:
        raise ValueError("original matrix SHA-256 mismatch")
    raw=json.loads(data)
    if int(raw["d"])!=int(header["d"]) or raw["q_labels"]!=header["q_labels"]:
        raise ValueError("original matrix d or q labels differ")
    if raw.get("chart") not in ("a0=b1=1",{"a_fixed":0,"b_fixed":1}):
        raise ValueError("original matrix chart differs")
    if header.get("chart")!={"a_fixed":0,"b_fixed":1}:
        raise ValueError("certificate matrix chart differs")
    denominator=int(raw["denominator"])
    if denominator<=0 or denominator&(denominator-1):
        raise ValueError("original matrix denominator not dyadic")
    normalized=header["M"]
    shift=int(normalized["scale"])+denominator.bit_length()-1
    def same(encoded,original):
        encoded,original=int(encoded),int(original)
        return encoded<<shift==original if shift>=0 else encoded==original<<(-shift)
    re,im=raw["real_numerators"],raw["imag_numerators"]
    rows=normalized["rows"]
    if len(re)!=len(rows) or len(im)!=len(rows):
        raise ValueError("original matrix shape differs")
    for rr,ii,zz in zip(re,im,rows):
        if len(rr)!=len(zz) or len(ii)!=len(zz):
            raise ValueError("original matrix row shape differs")
        if any(not same(z[0],r) or not same(z[1],i) for r,i,z in zip(rr,ii,zz)):
            raise ValueError("certificate matrix entry differs from original matrix")
    return {"file":str(path),"sha256":digest,"exact_entries_verified":True}


class SpurSystem:
    """Independently built signed-pair q, Jacobian, and group-action checks."""

    def __init__(self, header: dict, bits: int = 384, base_dir=None):
        self.header = header
        self.ctx = FixedContext(bits)
        ctx = self.ctx
        self.d = int(header["d"])
        d = self.d
        self.n = 2*d-2
        chart = header.get("chart",{})
        self.ac = int(chart.get("a_fixed",chart.get("c",0)))
        self.bs = int(chart.get("b_fixed",chart.get("s",1)))
        if self.ac != 0 or self.bs != 1:
            raise ValueError("canonical a0=b1=1 chart required")
        if header.get("q_scaling","original") != "original":
            raise ValueError("unscaled original q required")
        self.labels = [tuple(map(int,p)) for p in header["q_labels"]]
        self.matrix_binding=verify_matrix_binding(header,base_dir)
        seen = set()
        canonical = []
        for i in range(d):
            for j in range(d):
                if (i,j)==(0,0) or (i,j) in seen:
                    continue
                seen.update(((i,j),((-i)%d,(-j)%d)))
                canonical.append((i,j))
        if self.labels != canonical:
            raise ValueError("q_labels do not match original signed-pair order")
        self.M = _matrix_from_header(header,ctx)
        if len(self.M) != self.n or any(len(row)!=len(self.labels) for row in self.M):
            raise ValueError("M has wrong dimensions")
        if any(not ctx.exact(z) for row in self.M for z in row):
            raise ValueError("precision does not exactly represent M")
        ow = header["omega"]
        self.omega = ctx.rect(ow["real"],ow["imag"],int(ow["scale"]))
        # Authenticate the original fine enclosure with guard bits.  Merely
        # widening a 2^-512 box to a 2^-384 grid would leave no arithmetic
        # room for a strict Krawczyk inclusion at that coarse precision.
        auth_ctx=FixedContext(max(bits,-int(ow["scale"])+96))
        auth_omega=auth_ctx.rect(ow["real"],ow["imag"],int(ow["scale"]))
        self.omega_proof = certify_omega(auth_ctx,d,auth_omega)
        self.powers = [ctx.one]
        for _ in range(1,d):
            self.powers.append(ctx.mul(self.powers[-1],self.omega))
        self.groups = [(s,i,j) for s in (1,-1) for i in range(d) for j in range(d)
                       if (s,i,j)!=(1,0,0)]
        self.a_indices = [k for k in range(d) if k != self.ac]
        self.b_indices = [k for k in range(d) if k != self.bs]

    def center(self, record):
        cc = record.get("c",record.get("center"))
        scale = int(record.get("c_scale",record.get("center_scale",-192)))
        if len(cc) != self.n:
            raise ValueError("center length mismatch")
        result = [self.ctx.dyadic(*z,scale=scale) for z in cc]
        if any(not self.ctx.exact(z) for z in result):
            raise ValueError("center does not fit fixed-point precision exactly")
        return result

    def radius(self, record):
        exponent = int(record["radius_exp"])
        radius = self.ctx.dyadic(1,scale=exponent)
        if not self.ctx.exact(radius) or radius[0] <= 0:
            raise ValueError("radius does not fit precision exactly")
        return radius[0]

    def box(self, record):
        radius = self.radius(record)
        return [self.ctx.inflate(z,radius) for z in self.center(record)]

    def unpack(self, coords):
        if len(coords) != self.n:
            raise ValueError("wrong coordinate length")
        a = [self.ctx.one]*self.d
        b = [self.ctx.one]*self.d
        for k,z in zip(self.a_indices,coords[:self.d-1]): a[k]=z
        for k,z in zip(self.b_indices,coords[self.d-1:]): b[k]=z
        return a,b

    def evaluate_q(self, coords, jacobian=False):
        """q=(omega^(ij) U_ij V_ij)-S^2/(d+1), a-index expansion.

        U_ij=sum_k a_k b_(k+i) omega^(jk)
        V_ij=sum_l a_l b_(l-i) omega^(-jl).
        This is the product of the original signed displacement pair: the
        two tau phases multiply to omega^(ij), including in even dimension.
        """
        ctx,d = self.ctx,self.d
        add,mul,sub = ctx.add,ctx.mul,ctx.sub
        a,b = self.unpack(coords)
        S = ctx.sum(mul(a[k],b[k]) for k in range(d))
        sterm = ctx.div_int(mul(S,S),d+1)
        ds = [b[k] for k in self.a_indices] + [a[k] for k in self.b_indices]
        dsq = [ctx.div_int(ctx.mul_int(mul(S,dd),2),d+1) for dd in ds] if jacobian else None
        q, jac = [],[]
        # Cache shifted products once per i and the character values once per j.
        shifted = {}
        for i,j in self.labels:
            if i not in shifted:
                shifted[i] = [mul(a[k],b[(k+i)%d]) for k in range(d)]
                shifted[(-i)%d] = [mul(a[k],b[(k-i)%d]) for k in range(d)]
            up = [self.powers[j*k%d] for k in range(d)]
            vp = [self.powers[-j*k%d] for k in range(d)]
            U = ctx.sum(mul(shifted[i][k],up[k]) for k in range(d))
            V = ctx.sum(mul(shifted[(-i)%d][k],vp[k]) for k in range(d))
            phase = self.powers[i*j%d]
            q.append(sub(mul(phase,mul(U,V)),sterm))
            if jacobian:
                row=[]
                for col,k in enumerate(self.a_indices):
                    du = mul(b[(k+i)%d],up[k])
                    dv = mul(b[(k-i)%d],vp[k])
                    row.append(sub(mul(phase,add(mul(du,V),mul(U,dv))),dsq[col]))
                for off,k in enumerate(self.b_indices,start=d-1):
                    ku,kv=(k-i)%d,(k+i)%d
                    du = mul(a[ku],up[ku])
                    dv = mul(a[kv],vp[kv])
                    row.append(sub(mul(phase,add(mul(du,V),mul(U,dv))),dsq[off]))
                jac.append(row)
        return (q,jac) if jacobian else q

    def left_inverse_product(self, record):
        """B=A*M is combined at exact dyadic precision, then applied to q."""
        ctx = self.ctx
        scale = int(record.get("A_scale",record.get("inverse_scale",-128)))
        A = [[ctx.dyadic(*z,scale=scale) for z in row] for row in record["A"]]
        if len(A)!=self.n or any(len(row)!=self.n for row in A):
            raise ValueError("A has wrong dimensions")
        if any(not ctx.exact(z) for row in A for z in row):
            raise ValueError("precision does not exactly represent A")
        B = [[ctx.sum(ctx.mul(A[i][k],self.M[k][j]) for k in range(self.n))
              for j in range(len(self.labels))] for i in range(self.n)]
        if any(not ctx.exact(z) for row in B for z in row):
            raise ValueError("precision does not exactly represent A*M")
        return B

    def check_freeness(self, X, witnesses=None):
        """For every nonidentity g, exclude one projective a-wedge zero.

        g=X^i Z^j P^((1-s)/2), s in {+1,-1}, acts after removing a phase as
        a'_k=omega^(jk)*a_[s(k-i)].  The a0 chart supplies a_0=1.
        These are the same 2*d*d projective transformations for even d too.
        """
        ctx,d=self.ctx,self.d
        a,_=self.unpack(X)
        if witnesses is not None and len(witnesses)!=len(self.groups):
            raise ValueError("wrong number of freeness witnesses")
        out=[]
        for number,(s,i,j) in enumerate(self.groups):
            use = range(1,d) if witnesses is None else [int(witnesses[number])]
            found=None
            for k in use:
                if not 1 <= k < d:
                    raise ValueError("a-wedge witness index out of range")
                wedge = ctx.sub(ctx.mul(self.powers[j*k%d],a[s*(k-i)%d]),
                                ctx.mul(a[k],a[-s*i%d]))
                if ctx.excludes_zero(wedge):
                    found=k
                    break
            if found is None:
                raise ValueError(f"freeness not certified at group {(s,i,j)}")
            out.append(found)
        return out

    def check_record(self, record, check_freeness=True):
        """Strict contraction certifies one root, uniqueness and invertibility.

        beta=max_i ||(A F(c))_i||_1 and eta=max_i sum_j
        ||(I-A J(X))_ij||_1 are recomputed, with exact outward arithmetic.
        beta+eta*r<r and eta<1 imply T(x)=x-A F(x) maps X strictly into
        itself and contracts in the real-rectangle sup norm.  Banach gives a
        root of F because A is invertible: eta<1 implies A J(c) invertible,
        so the square matrix A is invertible.  It also proves J everywhere
        on X invertible by the same Neumann-series criterion.
        """
        ctx=self.ctx
        c=self.center(record)
        r=self.radius(record)
        X=[ctx.inflate(z,r) for z in c]
        qc=self.evaluate_q(c)
        qX,jq=self.evaluate_q(X,jacobian=True)
        B=self.left_inverse_product(record)
        residual=[ctx.sum(ctx.mul(bb,qq) for bb,qq in zip(row,qc)) for row in B]
        beta=max(map(ctx.abs1_upper,residual))
        eta=0
        for i,row in enumerate(B):
            bound=0
            for col in range(self.n):
                value=ctx.sum(ctx.mul(row[k],jq[k][col]) for k in range(len(self.labels)))
                target=ctx.one if i==col else ctx.zero
                bound+=ctx.abs1_upper(ctx.sub(target,value))
            eta=max(eta,bound)
        if eta >= ctx.S:
            raise ValueError("Jacobian contraction eta>=1")
        # Compare without any rounding of the scalar beta+eta*r.
        margin=r*ctx.S-beta*ctx.S-eta*r
        if margin <= 0:
            raise ValueError("strict root inclusion failed")
        witness=record.get("q_witness",record.get("q_witness_index"))
        if witness is None:
            witness=next((k for k,z in enumerate(qX) if ctx.excludes_zero(z)),None)
        if witness is None or not 0<=int(witness)<len(qX) or not ctx.excludes_zero(qX[int(witness)]):
            raise ValueError("q!=0 witness failed")
        free=self.check_freeness(X,record.get("free_witnesses")) if check_freeness else None
        return {"id":record.get("id"),"passed":True,"beta_upper":str(beta),
                "eta_upper":str(eta),"scale":-ctx.bits,"strict_margin_numerator":str(margin),
                "strict_margin_scale":-2*ctx.bits,"q_witness":int(witness),
                "free_witnesses":free,"group_order":2*self.d*self.d}


def load_json(path):
    with open(path) as handle:
        return json.load(handle)


def records_from_file(path):
    opener=gzip.open if str(path).endswith(".gz") else open
    with opener(path,"rt") as handle:
        for line_number,line in enumerate(handle,1):
            if line.strip():
                try:
                    yield json.loads(line)
                except Exception as error:
                    raise ValueError(f"{path}:{line_number}: {error}") from error


def invariant_interval(system, record, raw_q_indices, functional_num, functional_den):
    """Re(sum num_k*q_k / sum den_k*q_k), without trusted ball bounds."""
    ctx=system.ctx
    indices=list(map(int,raw_q_indices))
    if len(indices)!=len(set(indices)) or not all(0<=k<len(system.labels) for k in indices):
        raise ValueError("invalid invariant raw q indices")
    if len(indices)!=len(functional_num) or len(indices)!=len(functional_den):
        raise ValueError("invariant functional dimension mismatch")
    q=system.evaluate_q(system.box(record))
    numerator=ctx.sum(ctx.mul(ctx.dyadic(*coefficient),q[k])
                      for k,coefficient in zip(indices,functional_num))
    denominator=ctx.sum(ctx.mul(ctx.dyadic(*coefficient),q[k])
                        for k,coefficient in zip(indices,functional_den))
    if not ctx.excludes_zero(denominator):
        raise ValueError("invariant denominator may vanish")
    value=ctx.div(numerator,denominator)
    return value[0],value[1]


def file_sha256(path):
    digest=hashlib.sha256()
    with open(path,"rb") as handle:
        for block in iter(lambda:handle.read(1048576),b""):
            digest.update(block)
    return digest.hexdigest()


def _resolve_file(name, manifest_path):
    path=Path(name)
    if path.exists():
        return path
    candidate=Path(manifest_path).parent/path
    if candidate.exists():
        return candidate
    raise FileNotFoundError(name)


def check_separation(manifest_path, header_path=None, certificate_paths=None, bits=384):
    """Exhaustive interval separation of all represented projective orbits.

    The manifest's order is an untrusted sorting proposal.  Every invariant
    interval is recomputed, all ids must occur exactly once, and strict real
    separation is checked at every adjacent pair.  Thus transitivity proves
    separation of every pair, without checking only a nearest-neighbour sample.
    """
    manifest_digest=file_sha256(manifest_path)
    manifest=load_json(manifest_path)
    if manifest.get("schema")!="spur-invariant-separation-v1":
        raise ValueError("unknown separation manifest schema")
    if header_path is None:
        header_path=_resolve_file(manifest["header_file"],manifest_path)
    header_digest=file_sha256(header_path)
    if manifest.get("header_sha256")!=header_digest:
        raise ValueError("separation header hash mismatch")
    entries=manifest.get("certificate_files",manifest.get("certificate_chunks"))
    if not isinstance(entries,list) or not entries:
        raise ValueError("missing certificate chunk hashes")
    named={str(item.get("file",item.get("path"))):item["sha256"] for item in entries}
    if len(named)!=len(entries):
        raise ValueError("duplicate certificate chunk entry")
    if certificate_paths is None:
        certificate_paths=[_resolve_file(name,manifest_path) for name in named]
    if len(certificate_paths)!=len(named):
        raise ValueError("certificate chunk set mismatch")
    expected_by_basename={Path(name).name:digest for name,digest in named.items()}
    if len(expected_by_basename)!=len(named):
        raise ValueError("ambiguous certificate basename")
    certificate_digests={str(path):file_sha256(path) for path in certificate_paths}
    for path in certificate_paths:
        if certificate_digests[str(path)]!=expected_by_basename.get(Path(path).name):
            raise ValueError(f"separation certificate hash mismatch: {path}")
    system=SpurSystem(load_json(header_path),bits,base_dir=Path(header_path).parent)
    if "matrix_sha256" in manifest:
        if system.matrix_binding is None or manifest["matrix_sha256"]!=system.matrix_binding["sha256"]:
            raise ValueError("separation original matrix binding mismatch")
    artifact_digests={}
    for prefix in ("basis","system","individual_manifest"):
        key=prefix+"_file"
        if key in manifest:
            path=_resolve_file(manifest[key],manifest_path)
            digest=file_sha256(path)
            if manifest.get(prefix+"_sha256")!=digest:
                raise ValueError(f"separation {prefix} hash mismatch")
            artifact_digests[str(path)]=digest
            if prefix=="individual_manifest":
                individual=load_json(path)
                source_chunks={Path(item["file"]).name:item["sha256"] for item in individual["chunks"]}
                if source_chunks!=expected_by_basename:
                    raise ValueError("separation chunks differ from the individual-root manifest")
                if individual["header_sha256"]!=header_digest:
                    raise ValueError("individual-root manifest header binding mismatch")
    raw_indices=manifest["raw_q_indices"]
    num=manifest["functional_num"]
    den=manifest["functional_den"]
    order=manifest["order"]
    if len(order)!=len(set(order)):
        raise ValueError("repeated id in separation order")
    intervals={}
    for path in certificate_paths:
        for record in records_from_file(path):
            identity=record.get("id")
            if identity is None or identity in intervals:
                raise ValueError("missing or repeated certificate id")
            intervals[identity]=invariant_interval(system,record,raw_indices,num,den)
    if set(order)!=set(intervals):
        raise ValueError("separation order does not enumerate exact full certificate set")
    gaps=[]
    for left,right in zip(order,order[1:]):
        gap=intervals[right][0]-intervals[left][1]
        if gap<=0:
            raise ValueError(f"strict adjacent invariant separation failed: {left}, {right}")
        gaps.append(gap)
    if manifest_digest!=file_sha256(manifest_path) or header_digest!=file_sha256(header_path):
        raise ValueError("manifest or header changed during replay")
    if any(file_sha256(path)!=certificate_digests[str(path)] for path in certificate_paths):
        raise ValueError("certificate changed during separation replay")
    if any(file_sha256(path)!=digest for path,digest in artifact_digests.items()):
        raise ValueError("auxiliary artifact changed during separation replay")
    return {"passed":True,"checked_representatives":len(order),
            "checked_adjacent_pairs":len(gaps),"all_pairwise_separation":True,
            "representative_ids_sha256":hashlib.sha256(json.dumps(sorted(order),separators=(",",":")).encode()).hexdigest(),
            "minimum_adjacent_gap":str(min(gaps)) if gaps else None,"scale":-bits,
            "manifest_sha256":manifest_digest,
            "header_sha256":header_digest,
            "certificate_sha256":certificate_digests,
            "matrix_binding":system.matrix_binding,
            "auxiliary_artifact_sha256":artifact_digests,
            "certified_points_if_all_roots_replayed":len(order)*2*system.d*system.d,
            "note":"Root existence, nonsingularity and freeness require the root replay result too."}


_WORKER_SYSTEM=None


def _worker_init(header,bits,base_dir=None):
    global _WORKER_SYSTEM
    _WORKER_SYSTEM=SpurSystem(header,bits,base_dir=base_dir)


def _worker_check(record):
    return _WORKER_SYSTEM.check_record(record)


def _all_records(paths,limit=None):
    count=0
    for path in paths:
        for record in records_from_file(path):
            if limit is not None and count>=limit:
                return
            count+=1
            yield record


def selftest():
    """Remote-only deterministic checks against exact Fraction arithmetic."""
    from fractions import Fraction
    import random
    ctx=FixedContext(256)
    rng=random.Random(20261102)
    cases=0
    # Random endpoint combinations check every sign configuration, including
    # negative directed division. Fractions are an independent exact oracle.
    for _ in range(2000):
        raw=[rng.randrange(-100000,100001) for _ in range(8)]
        z=ctx.rect(sorted(raw[:2]),sorted(raw[2:4]),-20)
        w=ctx.rect(sorted(raw[4:6]),sorted(raw[6:]),-20)
        product=ctx.mul(z,w)
        quotient=ctx.div(z,w) if ctx.excludes_zero(w) else None
        for zr in (z[0],z[1]):
            for zi in (z[2],z[3]):
                for wr in (w[0],w[1]):
                    for wi in (w[2],w[3]):
                        rp=Fraction(zr*wr-zi*wi,ctx.S)
                        ip=Fraction(zr*wi+zi*wr,ctx.S)
                        assert product[0]<=rp<=product[1]
                        assert product[2]<=ip<=product[3]
                        if quotient is not None:
                            den=wr*wr+wi*wi
                            rq=Fraction((zr*wr+zi*wi)*ctx.S,den)
                            iq=Fraction((zi*wr-zr*wi)*ctx.S,den)
                            assert quotient[0]<=rq<=quotient[1]
                            assert quotient[2]<=iq<=quotient[3]
                        cases+=1
    # Approximate literals are untrusted proposals. certify_omega must prove
    # enclosure from Phi_d itself, and a shifted false proposal must be rejected.
    literals={6:("0.5","0.8660254037844386467637231707529361834714026269051903140279034897259665084544"),
              7:("0.6234898018587335305250048840042398106322747308964021053655494396547324960692",
                 "0.7818314824680298087084445266740577502323345187086875289806347821124256170645")}
    proofs=[]
    polynomial_checks=0
    for d,(re,im) in literals.items():
        re=Fraction(re); im=Fraction(im)
        rr=int(re*ctx.S); ii=int(im*ctx.S)
        r=1<<(ctx.bits-180)
        box=ComplexBox(rr-r,rr+r,ii-r,ii+r)
        proofs.append(certify_omega(ctx,d,box))
        try:
            certify_omega(ctx,d,ctx.add(box,ctx.dyadic(1,scale=-40)))
        except ValueError:
            pass
        else:
            raise AssertionError("false omega enclosure was accepted")
        # Separately expand the original signed-pair product as d*d terms.
        # Gaussian integer values and the product rule supply a second q/J
        # implementation, used only as a deterministic calibration oracle.
        seen=set(); labels=[]
        for i in range(d):
            for j in range(d):
                if (i,j)==(0,0) or (i,j) in seen: continue
                seen.update(((i,j),((-i)%d,(-j)%d)))
                labels.append([i,j])
        M={"scale":0,"rows":[[[int(i==j),0] for j in range(len(labels))] for i in range(2*d-2)]}
        header={"d":d,"q_labels":labels,"M":M,"omega":ctx.encode(box),
                "chart":{"a_fixed":0,"b_fixed":1},"q_scaling":"original"}
        system=SpurSystem(header,bits=256)
        def gm(z,w):
            return z[0]*w[0]-z[1]*w[1], z[0]*w[1]+z[1]*w[0]
        def gp(values):
            result=(1,0)
            for value in values: result=gm(result,value)
            return result
        for _ in range(3):
            values=[(rng.randrange(-4,5),rng.randrange(-4,5)) for _ in range(system.n)]
            coords=[ctx.dyadic(*z) for z in values]
            a=[(1,0)]+values[:d-1]
            b=[values[d-1],(1,0)]+values[d:]
            ab=a+b
            free=list(range(1,d))+[d]+list(range(d+2,2*d))
            q,jac=system.evaluate_q(coords,True)
            S=(sum(gm(a[k],b[k])[0] for k in range(d)),
               sum(gm(a[k],b[k])[1] for k in range(d)))
            Ssq=ctx.dyadic(*gm(S,S))
            for row,(i,j) in enumerate(labels):
                terms=[]; dterms=[[] for _ in free]
                for k in range(d):
                    for l in range(d):
                        indices=(k,l,d+(k+i)%d,d+(l-i)%d)
                        char=system.powers[j*(i+k-l)%d]
                        terms.append(ctx.mul(ctx.dyadic(*gp(ab[t] for t in indices)),char))
                        for col,var in enumerate(free):
                            for factor,index in enumerate(indices):
                                if index==var:
                                    scalar=gp(ab[t] for nn,t in enumerate(indices) if nn!=factor)
                                    dterms[col].append(ctx.mul(ctx.dyadic(*scalar),char))
                oracle=ctx.sub(ctx.sum(terms),ctx.div_int(Ssq,d+1))
                if not (max(q[row][0],oracle[0])<=min(q[row][1],oracle[1]) and
                        max(q[row][2],oracle[2])<=min(q[row][3],oracle[3])):
                    raise AssertionError(f"direct q expansion mismatch d={d}, label={(i,j)}")
                polynomial_checks+=1
                for col,var in enumerate(free):
                    ds=b[var] if var<d else a[var-d]
                    oracle=ctx.sub(ctx.sum(dterms[col]),
                                   ctx.div_int(ctx.mul_int(ctx.dyadic(*gm(S,ds)),2),d+1))
                    observed=jac[row][col]
                    if not (max(observed[0],oracle[0])<=min(observed[1],oracle[1]) and
                            max(observed[2],oracle[2])<=min(observed[3],oracle[3])):
                        raise AssertionError(f"direct J expansion mismatch d={d}, label={(i,j)}, col={col}")
                    polynomial_checks+=1
    return {"passed":True,"arithmetic_endpoint_checks":cases,"omega_proofs":proofs,
            "direct_signed_pair_q_and_jacobian_checks":polynomial_checks,
            "python":platform.python_version(),"platform":platform.platform(),
            "seed":20261102,"dependencies":"Python standard library only"}


def negative_selftest(header_path, certificate_paths, bits):
    """Reject deliberately corrupted real d6/d7 certificate inputs."""
    from copy import deepcopy
    header=load_json(header_path)
    record=next(_all_records(certificate_paths,limit=1))
    system=SpurSystem(header,bits,base_dir=Path(header_path).parent)
    system.check_record(record)
    cases={}
    def reject(name, function):
        try:
            function()
        except (ValueError,ZeroDivisionError) as error:
            cases[name]={"rejected":True,"reason":str(error)}
        else:
            raise AssertionError(f"corrupted certificate accepted: {name}")
    wrong_center=deepcopy(record)
    shift=max(0,-int(record["c_scale"]))
    wrong_center["c"][0][0]=str(int(wrong_center["c"][0][0])+(1<<shift))
    reject("center_shifted_by_at_least_one",lambda:system.check_record(wrong_center))
    zero_inverse=deepcopy(record)
    zero_inverse["A"]=[[["0","0"] for _ in range(system.n)] for _ in range(system.n)]
    reject("zero_inverse",lambda:system.check_record(zero_inverse))
    false_free=deepcopy(record)
    false_free["free_witnesses"]=[0]*len(system.groups)
    reject("zero_wedge_witnesses",lambda:system.check_record(false_free))
    false_q=deepcopy(record)
    false_q["q_witness"]=len(system.labels)
    reject("invalid_q_witness",lambda:system.check_record(false_q))
    false_omega=deepcopy(header)
    shift=max(0,-int(false_omega["omega"]["scale"]))
    false_omega["omega"]["real"]=[str(int(x)+(1<<shift)) for x in false_omega["omega"]["real"]]
    reject("omega_shifted_by_at_least_one",lambda:SpurSystem(false_omega,bits,base_dir=Path(header_path).parent))
    if "matrix_file" in header:
        false_matrix=deepcopy(header)
        false_matrix["M"]["rows"][0][0][0]=str(int(false_matrix["M"]["rows"][0][0][0])+1)
        reject("one_changed_exact_matrix_numerator",lambda:SpurSystem(false_matrix,bits,base_dir=Path(header_path).parent))
    return {"passed":True,"baseline_id":record["id"],"negative_cases":cases,"bits":bits,
            "header_sha256":file_sha256(header_path),
            "certificate_sha256":{str(path):file_sha256(path) for path in certificate_paths},
            "python":platform.python_version(),"dependencies":"Python standard library only"}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--header")
    parser.add_argument("--certificates",nargs="+")
    parser.add_argument("--bits",type=int,default=384)
    parser.add_argument("--output",required=True)
    parser.add_argument("--results")
    parser.add_argument("--limit",type=int)
    parser.add_argument("--selftest",action="store_true")
    parser.add_argument("--negative-selftest",action="store_true")
    parser.add_argument("--separation")
    parser.add_argument("--workers",type=int,default=1)
    args=parser.parse_args()
    start=time.monotonic()
    checker_digest=file_sha256(__file__)
    if args.selftest:
        result=selftest()
    elif args.negative_selftest:
        if not args.header or not args.certificates:
            parser.error("--header and --certificates required for negative selftest")
        result=negative_selftest(args.header,args.certificates,args.bits)
    elif args.separation:
        result=check_separation(args.separation,args.header,args.certificates,args.bits)
        result.update({"checker_sha256":checker_digest,"python":platform.python_version(),
                       "dependencies":"Python standard library only"})
    else:
        if not args.header or not args.certificates:
            parser.error("--header and --certificates are required for replay")
        header_digest=file_sha256(args.header)
        certificate_digests={str(path):file_sha256(path) for path in args.certificates}
        header=load_json(args.header)
        system=SpurSystem(header,args.bits,base_dir=Path(args.header).parent)
        if not 1<=args.workers<=4:
            parser.error("--workers must be between 1 and 4")
        count=0
        ids=set()
        out=open(args.results,"w") if args.results else None
        pool=None
        try:
            records=_all_records(args.certificates,args.limit)
            if args.workers>1:
                pool=multiprocessing.Pool(args.workers,initializer=_worker_init,
                                          initargs=(header,args.bits,str(Path(args.header).parent)))
                results=pool.imap(_worker_check,records,chunksize=1)
            else:
                results=map(system.check_record,records)
            for checked in results:
                identity=checked["id"]
                if identity is None or identity in ids:
                    raise ValueError("missing or repeated representative id")
                ids.add(identity)
                count+=1
                if out:
                    out.write(json.dumps(checked,separators=(",",":"))+"\n")
                    out.flush()
                if count%32==0:
                    print(json.dumps({"checked":count,"seconds":time.monotonic()-start}),flush=True)
        finally:
            if out: out.close()
            if pool:
                pool.close()
                pool.join()
        if header_digest!=file_sha256(args.header):
            raise ValueError("header changed during root replay")
        if any(file_sha256(path)!=certificate_digests[str(path)] for path in args.certificates):
            raise ValueError("certificate changed during root replay")
        result={"passed":True,"checked_representatives":count,
                "representative_ids_sha256":hashlib.sha256(json.dumps(sorted(ids),separators=(",",":")).encode()).hexdigest(),
                "certified_points_before_orbit_deduplication":count*2*system.d*system.d,
                "freeness_checks":count*(2*system.d*system.d-1),
                "omega":system.omega_proof,"bits":args.bits,
                "matrix_binding":system.matrix_binding,
                "header_sha256":header_digest,
                "certificate_sha256":certificate_digests,
                "checker_sha256":checker_digest,"python":platform.python_version(),
                "platform":platform.platform(),"dependencies":"Python standard library only",
                "note":"Orbit-to-orbit separation must also be checked before claiming the point total."}
    if checker_digest!=file_sha256(__file__):
        raise ValueError("checker source changed during this replay; repeat with immutable source")
    result["checker_sha256"]=checker_digest
    result["elapsed_seconds"]=time.monotonic()-start
    Path(args.output).write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,separators=(",",":")),flush=True)


if __name__=="__main__":
    main()
