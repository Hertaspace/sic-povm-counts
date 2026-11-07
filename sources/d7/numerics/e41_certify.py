#!/usr/bin/env python3
"""Arb/acb certificate producer for isolated off-base square-up roots.

Run with python-flint installed in the selected Python environment.
The portable certificate consists ONLY of exact dyadic data plus the exact M.
Reported numerical bounds are diagnostics; an independent checker recomputes them.
No monodromy count is a certified count.  Seed: 20261102.
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
from datetime import datetime, timezone
import hashlib
import importlib.metadata
import json
from pathlib import Path
import platform
import sys
import time

from flint import acb, acb_mat, arb, ctx, fmpq

SEED = 20261102
SCHEMA = "sic-spur-balls-v1"


def sha256_file(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def dyadic(integer, scale=0):
    """Exact arb value integer * 2**scale."""
    integer, scale = int(integer), int(scale)
    if scale >= 0:
        return arb(integer << scale)
    return arb(fmpq(integer, 1 << -scale))


def _endpoint_integer(endpoint, scale, upper):
    mantissa, exponent = endpoint.man_exp()
    mantissa, shift = int(mantissa), int(exponent) - int(scale)
    if shift >= 0:
        return mantissa << shift
    divisor = 1 << -shift
    return -((-mantissa) // divisor) if upper else mantissa // divisor


def outward_dyadic(ball, scale=-256):
    """Return [floor(lower/2**scale), ceil(upper/2**scale)] as strings.

    Thus returned integers, multiplied by 2**scale, enclose the input arb ball.
    No floating-point conversion occurs.
    """
    if not ball.is_finite():
        raise ValueError("nonfinite ball")
    return [str(_endpoint_integer(ball.lower(), scale, False)),
            str(_endpoint_integer(ball.upper(), scale, True))]


def arb_from_interval(pair, scale):
    lo, hi = map(int, pair)
    if lo > hi:
        raise ValueError("reversed interval")
    return arb(dyadic(lo + hi, int(scale) - 1), dyadic(hi - lo, int(scale) - 1))


def acb_from_pair(pair, scale):
    return acb(dyadic(pair[0], scale), dyadic(pair[1], scale))


def quantize_component(ball, scale):
    """Round an arb midpoint to the specified exact dyadic lattice."""
    mantissa, exponent = ball.mid().man_exp()
    mantissa, shift = int(mantissa), int(exponent) - int(scale)
    if shift >= 0:
        return str(mantissa << shift)
    sign = -1 if mantissa < 0 else 1
    denominator_bits = -shift
    rounded = (abs(mantissa) + (1 << (denominator_bits - 1))) >> denominator_bits
    return str(sign * rounded)


def quantize_complex(ball, scale):
    return [quantize_component(ball.real, scale), quantize_component(ball.imag, scale)]


def complex_l1_upper(ball):
    # Return an exact dyadic upper endpoint.  Taking max() of overlapping arb
    # intervals would not itself be a rigorous maximum operation.
    return (abs(ball.real).upper() + abs(ball.imag).upper()).upper()


def excludes_zero(ball):
    return not ball.contains(0)


def box_from_certificate(record):
    radius = dyadic(1, record["radius_exp"])
    scale = record["c_scale"]
    return [acb(arb(dyadic(v[0], scale), radius), arb(dyadic(v[1], scale), radius))
            for v in record["c"]]


def center_from_certificate(record):
    return [acb_from_pair(v, record["c_scale"]) for v in record["c"]]


def inverse_from_certificate(record):
    return acb_mat([[acb_from_pair(v, record["A_scale"]) for v in row] for row in record["A"]])


def raw_labels(d):
    seen, labels = set(), []
    for i in range(d):
        for j in range(d):
            if (i, j) == (0, 0) or (i, j) in seen:
                continue
            seen.update(((i, j), ((-i) % d, (-j) % d)))
            labels.append([i, j])
    return labels


class CertifiedSystem:
    """Exact-M system with a certified rectangle for omega=exp(2*pi*i/d).

    q_balls() returns full raw q, without a (d+1) rescaling.  This public API is
    also used by e43; it does not read any floating-point root data.
    """
    def __init__(self, header):
        self.header = header
        self.d = int(header["d"])
        self.n = 2 * self.d - 2
        self.labels = header["q_labels"]
        if self.labels != raw_labels(self.d):
            raise ValueError("q labels differ from canonical raw list")
        if header["chart"] != {"a_fixed": 0, "b_fixed": 1}:
            raise ValueError("unsupported chart")
        if header.get("q_scaling") != "original":
            raise ValueError("expected original unscaled q")
        om = header["omega"]
        self.omega = acb(arb_from_interval(om["real"], om["scale"]),
                         arb_from_interval(om["imag"], om["scale"]))
        self.powers = [acb(1)]
        for _ in range(1, self.d):
            self.powers.append(self.powers[-1] * self.omega)
        mat = header["M"]
        if len(mat["rows"]) != self.n or any(len(row) != len(self.labels) for row in mat["rows"]):
            raise ValueError("incorrect M shape")
        self.M = acb_mat([[acb_from_pair(z, mat["scale"]) for z in row] for row in mat["rows"]])
        self.variable_coordinates = [("a", k) for k in range(1, self.d)] + [("b", 0)] + [("b", k) for k in range(2, self.d)]

    def full_ab(self, x):
        if len(x) != self.n:
            raise ValueError("incorrect root dimension")
        a = [acb(1)] + list(x[:self.d - 1])
        b = [x[self.d - 1], acb(1)] + list(x[self.d:])
        return a, b

    def q_balls(self, x):
        return self.q_and_jac(x, False)[0]

    def q_and_jac(self, x, want_jac=True):
        d, powers = self.d, self.powers
        a, b = self.full_ab(x)
        S = sum((a[k] * b[k] for k in range(d)), acb(0))
        Ssquare = S * S / (d + 1)
        if want_jac:
            dS = [b[k] if typ == "a" else a[k] for typ, k in self.variable_coordinates]
            factorS = 2 * S / (d + 1)
        q, jac = [], []
        for i, j in self.labels:
            U = sum((b[k] * a[(k-i) % d] * powers[(j*k) % d] for k in range(d)), acb(0))
            V = sum((b[k] * a[(k+i) % d] * powers[(-j*k) % d] for k in range(d)), acb(0))
            phase = powers[(-i*j) % d]
            q.append(phase * U * V - Ssquare)
            if want_jac:
                row = []
                for t, (typ, k) in enumerate(self.variable_coordinates):
                    if typ == "a":
                        dU = b[(k+i) % d] * powers[(j*(k+i)) % d]
                        dV = b[(k-i) % d] * powers[(-j*(k-i)) % d]
                    else:
                        dU = a[(k-i) % d] * powers[(j*k) % d]
                        dV = a[(k+i) % d] * powers[(-j*k) % d]
                    row.append(phase * (dU * V + U * dV) - factorS * dS[t])
                jac.append(row)
        return q, acb_mat(jac) if want_jac else None

    def F_and_jac(self, x):
        q, jac = self.q_and_jac(x)
        return self.M * acb_mat([[z] for z in q]), self.M * jac

    def free_witnesses(self, x):
        a, _ = self.full_ab(x)
        witnesses = []
        for parity in (1, -1):
            for i in range(self.d):
                for j in range(self.d):
                    if (parity, i, j) == (1, 0, 0):
                        continue
                    fixed0 = a[(parity * -i) % self.d]
                    for k in range(self.d):
                        wedge = self.powers[(j*k) % self.d] * a[(parity*(k-i)) % self.d] - a[k] * fixed0
                        if excludes_zero(wedge):
                            witnesses.append(k)
                            break
                    else:
                        raise ValueError(f"a-only freeness unproved for g={(parity,i,j)}")
        return witnesses


def make_header(matrix_path, prec=768, omega_scale=-512):
    matrix_path = Path(matrix_path)
    raw = json.loads(matrix_path.read_text())
    d = int(raw["d"])
    n = 2*d - 2
    denominator = int(raw["denominator"])
    if denominator <= 0 or denominator & (denominator - 1):
        raise ValueError("M denominator must be a power of two")
    scale = -(denominator.bit_length() - 1)
    real, imag = raw["real_numerators"], raw["imag_numerators"]
    if len(real) != n or len(imag) != n:
        raise ValueError("invalid matrix rows")
    labels = raw["q_labels"]
    if labels != raw_labels(d):
        raise ValueError("invalid raw q labels")
    if any(len(row) != len(labels) for row in real + imag):
        raise ValueError("invalid matrix columns")
    ctx.prec = int(prec)
    omega = acb(0, 2 * arb.pi() / d).exp()
    return {
        "schema_version": SCHEMA,
        "d": d,
        "seed": SEED,
        "chart": {"a_fixed": 0, "b_fixed": 1},
        "variable_order": [f"a{k}" for k in range(1,d)] + ["b0"] + [f"b{k}" for k in range(2,d)],
        "q_labels": labels,
        "q_scaling": "original",
        "q_formula": "omega^(-i*j)*(sum_k b_k*a_(k-i)*omega^(j*k))*(sum_k b_k*a_(k+i)*omega^(-j*k))-(sum_k a_k*b_k)^2/(d+1)",
        "M": {"scale": scale, "rows": [[[str(real[r][c]), str(imag[r][c])] for c in range(len(labels))] for r in range(n)]},
        "matrix_file": matrix_path.name,
        "matrix_sha256": sha256_file(matrix_path),
        "omega": {"scale": int(omega_scale), "real": outward_dyadic(omega.real, omega_scale), "imag": outward_dyadic(omega.imag, omega_scale)},
        "omega_construction_precision_bits": int(prec),
        "free_group_order": 2*d*d,
        "free_group_enumeration": "s=+1,-1; i=0..d-1; j=0..d-1; omit (+1,0,0)",
        "free_wedge": "omega^(j*k)*a_(s*(k-i))-a_k*a_(-s*i)",
        "norm": "real coordinate infinity norm; complex block row bound |Re|+|Im|",
        "generator_file": Path(__file__).name,
        "generator_sha256": sha256_file(__file__),
        "python_flint": importlib.metadata.version("python-flint"),
        "python": sys.version,
        "platform": platform.platform(),
    }


def refine(system, initial, precision=512, iterations=16, target_exp=-272):
    ctx.prec = precision
    x = [acb(arb(str(pair[0])), arb(str(pair[1]))) for pair in initial]
    target = dyadic(1, target_exp)
    history = []
    for iteration in range(iterations):
        F, J = system.F_and_jac(x)
        delta = J.solve(F)
        bound = max((complex_l1_upper(delta[k,0]) for k in range(system.n)), default=arb(0))
        history.append(str(bound))
        x = [acb_from_pair(quantize_complex(x[k] - delta[k,0], -precision + 64), -precision + 64) for k in range(system.n)]
        if bound < target:
            return x, history
    raise ValueError(f"Newton did not reach target after {iterations} steps; last correction {history[-1]}")


def verify_record(system, record, require_witnesses=True):
    """Recompute all sufficient inequalities; diagnostics never serve as input."""
    c = center_from_certificate(record)
    X = box_from_certificate(record)
    A = inverse_from_certificate(record)
    B = A * system.M
    qc = system.q_balls(c)
    qX, JqX = system.q_and_jac(X)
    residual = B * acb_mat([[z] for z in qc])
    beta = max(complex_l1_upper(residual[k,0]) for k in range(system.n))
    defect = acb_mat([[int(k == l) for l in range(system.n)] for k in range(system.n)]) - B * JqX
    eta = max(sum((complex_l1_upper(defect[k,l]) for l in range(system.n)), arb(0)).upper() for k in range(system.n))
    radius = dyadic(1, record["radius_exp"])
    total = beta + eta * radius
    if not eta < 1:
        raise ValueError(f"Jacobian defect bound not <1: {eta}")
    if not total < radius:
        raise ValueError(f"Krawczyk inclusion fails: beta={beta}, eta={eta}, radius={radius}")
    if require_witnesses:
        qw = record.get("q_witness")
        if qw is None:
            qw = next((k for k,z in enumerate(qX) if excludes_zero(z)), None)
        if qw is None or not excludes_zero(qX[qw]):
            raise ValueError("q!=0 unproved")
        free = system.free_witnesses(X)
        if "free_witnesses" in record and record["free_witnesses"] != free:
            # A different valid witness is allowed; verify the supplied one directly.
            a, _ = system.full_ab(X)
            supplied = iter(record["free_witnesses"])
            for s in (1,-1):
                for i in range(system.d):
                    for j in range(system.d):
                        if (s,i,j)==(1,0,0):
                            continue
                        k = next(supplied)
                        wedge=system.powers[(j*k)%system.d]*a[(s*(k-i))%system.d]-a[k]*a[(-s*i)%system.d]
                        if not excludes_zero(wedge):
                            raise ValueError("supplied free witness fails")
            free = record["free_witnesses"]
        record["q_witness"] = qw
        record["free_witnesses"] = free
    record["diagnostics"] = {"precision_bits": ctx.prec, "beta_upper": str(beta), "eta_upper": str(eta), "inclusion_over_radius": str(total/radius)}
    return record


def certify_point(system, point, identity, source, source_sha):
    failures = []
    for precision, cscale, ascale, radius_exp in ((512,-224,-160,-160), (768,-320,-320,-224), (1024,-448,-512,-288)):
        try:
            ctx.prec = precision
            x, history = refine(system, point, precision, target_exp=cscale-48)
            c = [quantize_complex(z,cscale) for z in x]
            xc = [acb_from_pair(z,cscale) for z in c]
            _, J = system.F_and_jac(xc)
            inv = J.inv()
            A = [[quantize_complex(inv[k,l],ascale) for l in range(system.n)] for k in range(system.n)]
            record = {"id": int(identity), "source_index": int(identity), "source_file": source,
                      "source_sha256": source_sha, "c_scale": cscale, "A_scale": ascale,
                      "radius_exp": radius_exp, "c": c, "A": A,
                      "newton_iterations": len(history)}
            return verify_record(system,record)
        except Exception as exc:
            failures.append({"precision_bits":precision,"error":repr(exc)})
    raise ValueError(json.dumps(failures))


def run_toy():
    ctx.prec = 512
    center = acb_from_pair(quantize_complex(acb(arb(2).sqrt()),-224),-224)
    radius = dyadic(1,-160)
    X = acb(arb(center.real,radius),arb(center.imag,radius))
    A = acb_from_pair(quantize_complex(1/(2*center),-160),-160)
    beta = complex_l1_upper(A*(center*center-2))
    eta = complex_l1_upper(1-A*(2*X))
    positive = bool(eta<1 and beta+eta*radius<radius)
    wrong_center = acb(1)
    bad_beta = complex_l1_upper(A*(wrong_center*wrong_center-2))
    negative = not bool(eta<1 and bad_beta+eta*radius<radius)
    result = {"schema":"sic-spur-toy-calibration-v1","seed":SEED,"precision_bits":ctx.prec,
              "equation":"z^2-2=0","positive_accept":positive,"wrong_center_reject":negative,
              "c_scale":-224,"c":quantize_complex(center,-224),"A_scale":-160,"A":quantize_complex(A,-160),
              "radius_exp":-160,"beta":str(beta),"eta":str(eta),"python_flint":importlib.metadata.version("python-flint")}
    if not positive or not negative:
        raise RuntimeError(result)
    Path("e41_toy_calibration.json").write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps(result,sort_keys=True),flush=True)


def certify_files(args):
    prefix = Path(args.output_prefix)
    header_path = prefix.with_name(prefix.name+"_header.json")
    if header_path.exists():
        header = json.loads(header_path.read_text())
        if header["matrix_sha256"] != sha256_file(args.matrix):
            raise ValueError("existing header refers to different matrix")
    else:
        header = make_header(args.matrix)
        header_path.write_text(json.dumps(header,indent=2,sort_keys=True)+"\n")
    ctx.prec = 512
    system = CertifiedSystem(header)
    manifest_path = prefix.with_name(prefix.name+"_manifest.json")
    existing_ids = set()
    chunks = []
    if manifest_path.exists():
        old = json.loads(manifest_path.read_text())
        for chunk in old.get("chunks",[]):
            path = Path(chunk["file"])
            if sha256_file(path) != chunk["sha256"]:
                raise ValueError("existing certificate chunk changed")
            for line in path.read_text().splitlines():
                existing_ids.add(int(json.loads(line)["id"]))
        chunks = old.get("chunks",[])
    pending, failures, total_new = [], [], 0
    started = time.monotonic()

    def flush():
        nonlocal pending
        if pending:
            name = prefix.with_name(prefix.name+f"_cert_{len(chunks)+1:06d}.jsonl")
            content = "".join(json.dumps(z,separators=(",",":"),sort_keys=True)+"\n" for z in pending)
            if len(content.encode()) >= 1048576:
                raise ValueError("certificate chunk exceeds 1 MiB")
            name.write_text(content)
            chunks.append({"file":str(name),"sha256":sha256_file(name),"count":len(pending),"ids":[z["id"] for z in pending]})
            pending=[]
        manifest = {"schema_version":SCHEMA,"header_file":str(header_path),"header_sha256":sha256_file(header_path),
                    "d":system.d,"seed":SEED,"generator_sha256":sha256_file(__file__),"chunks":chunks,
                    "certified_representatives":sum(c["count"] for c in chunks),
                    "free_orbit_size":2*system.d*system.d,
                    "certified_points_before_orbit_dedup":sum(c["count"] for c in chunks)*2*system.d*system.d,
                    "failures":failures,"elapsed_this_run_seconds":time.monotonic()-started,
                    "meaning":"Root boxes individually certified; distinct-orbit count requires e43 separation.",
                    "utc_updated":datetime.now(timezone.utc).isoformat()}
        manifest_path.write_text(json.dumps(manifest,indent=2,sort_keys=True)+"\n")

    stop_after = args.max_points
    for source_path in args.reps:
        source_path=Path(source_path)
        raw=json.loads(source_path.read_text())
        source_sha=sha256_file(source_path)
        if raw["matrix_sha256"] != header["matrix_sha256"] or int(raw["d"]) != system.d:
            raise ValueError("root chunk does not belong to matrix")
        for offset, point in enumerate(raw["points"]):
            identity=int(raw["first_index"])+offset
            if identity in existing_ids:
                continue
            if stop_after and total_new >= stop_after:
                flush()
                return
            try:
                record=certify_point(system,point,identity,source_path.name,source_sha)
                # Keep enough room for unusually large exact inverse numerators.
                if pending and (len(pending)>=args.chunk_size or sum(len(json.dumps(z)) for z in pending)+len(json.dumps(record))>850000):
                    flush()
                pending.append(record)
                existing_ids.add(identity)
                total_new+=1
            except Exception as exc:
                failures.append({"id":identity,"source_file":source_path.name,"error":repr(exc)})
                print(json.dumps({"failed_id":identity,"error":repr(exc)}),flush=True)
            if (total_new+len(failures)) % 10 == 0:
                print(json.dumps({"new_certified":total_new,"failures":len(failures),"last_id":identity,"elapsed_seconds":time.monotonic()-started}),flush=True)
            if len(pending)>=args.chunk_size:
                flush()
    flush()
    print(json.dumps({"complete":True,"new_certified":total_new,"failures":len(failures),"manifest":str(manifest_path)}),flush=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    sub=parser.add_subparsers(dest="command",required=True)
    sub.add_parser("toy")
    cert=sub.add_parser("certify")
    cert.add_argument("--matrix",required=True)
    cert.add_argument("--reps",nargs="+",required=True)
    cert.add_argument("--output-prefix",required=True)
    cert.add_argument("--max-points",type=int,default=0)
    cert.add_argument("--chunk-size",type=int,default=24)
    args=parser.parse_args()
    try:
        ctx.threads=1
    except AttributeError:
        pass
    if args.command=="toy":
        run_toy()
    else:
        certify_files(args)


if __name__=="__main__":
    main()
