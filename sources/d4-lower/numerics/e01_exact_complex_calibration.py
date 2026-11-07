#!/usr/bin/env python3
"""Exact d4 upper bound/orbits and d5 lower bound; read-only upstream inputs.

Python standard library plus Singular 4.4.1. Seed is recorded but there are
no randomized Python choices. All generated files stay under this agent dir.
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
from collections import Counter
from fractions import Fraction
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path
import platform
import re
import resource
import shutil
import subprocess
import sys
import time

sys.dont_write_bytecode = True
BASE = Path(__file__).resolve().parents[1]
REPO = public_root(__file__)
OLD = REPO / "sources/exact-d4-d5"
SEED = 20261024


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def poly_string(terms):
    chunks = []
    for monomial, coefficient in sorted(terms.items()):
        if coefficient:
            factors = "*".join(monomial)
            chunks.append(str(coefficient) + ("*" + factors if factors else ""))
    return "+".join(chunks).replace("+-", "-") or "0"


def equations(d, zero_ket=None):
    def xm(j):
        return () if j == 0 else (f"x{j}",)

    def ym(j):
        return (f"y{j}",)

    norm = Counter({(): -1})
    for j in range(d):
        if j != zero_ket:
            norm[tuple(sorted(xm(j) + ym(j)))] += 1
    result = [poly_string(norm)]
    for k, ell in product(range(d), repeat=2):
        terms = Counter({(): -(int(k == 0) + int(ell == 0))})
        for j in range(d):
            j2 = (j + k + ell) % d
            if zero_ket in (j, j2):
                continue
            mono = xm(j) + ym((j+k) % d) + ym((j+ell) % d) + xm(j2)
            terms[tuple(sorted(mono))] += d+1
        result.append(poly_string(terms))
    return result


def emit_singular(d, zero_ket=None, lift_unit=False):
    variables = [f"x{j}" for j in range(1, d) if j != zero_ket]
    variables += [f"y{j}" for j in range(d)]
    src = ["// Full trace-one Fourier equations, x0=1. Exact characteristic zero.",
           "ring R=0,(" + ",".join(variables) + "),dp;",
           "short=0; option(redSB);",
           "ideal I=" + ",".join(equations(d, zero_ket)) + ";",
           'print("INPUT_GENERATORS="+string(size(I)));',
           "ideal G=std(I);",
           'print("DIMENSION="+string(dim(G)));',
           'print("QUOTIENT_DIMENSION="+string(vdim(G)));',
           'print("GB_SIZE="+string(size(G)));',
           'ideal Rem=reduce(I,G); int rz=1; int ri;',
           'for(ri=1;ri<=size(Rem);ri++){if(Rem[ri]!=0){rz=0;}}',
           'print("GENERATOR_REMAINDERS_ZERO="+string(rz));']
    if lift_unit:
        src += ["if (size(G)==1 && G[1]==1) {",
                " matrix T=lift(I,G);",
                ' matrix Diff=matrix(I)*T-matrix(G); int lz=1; int li; int lj;',
                ' for(li=1;li<=nrows(Diff);li++){for(lj=1;lj<=ncols(Diff);lj++){if(Diff[li,lj]!=0){lz=0;}}}',
                ' print("UNIT_LIFT_ZERO="+string(lz));',
                ' int j; for(j=1;j<=size(I);j++){print("LIFT:"+string(j)+":"+string(T[j,1]));}',
                "}"]
    src += ['print("COMPLETE=1");', "quit;"]
    return "\n".join(src) + "\n"


def run_singular(path, seconds=60):
    executable = shutil.which("Singular")
    if not executable:
        return {"completed": False, "reason": "Singular unavailable"}
    outfile = path.with_suffix(".singular.out")
    command = [executable, "-q", "--random="+str(SEED), "--cpus=1",
               "--threads=1", "--flint-threads=1", "--no-rc", str(path)]
    start = time.monotonic()
    rssmax = None
    reason = None
    with outfile.open("w") as output:
        process = subprocess.Popen(command, stdout=output, stderr=subprocess.STDOUT)
        while process.poll() is None:
            elapsed = time.monotonic()-start
            if elapsed > seconds:
                reason = "wall limit"
                process.terminate()  # exact PID of the process started here
                try:
                    process.wait(timeout=2)
                except subprocess.TimeoutExpired:
                    process.kill()  # exact same owned PID
                    process.wait()
                break
            time.sleep(0.1)
    text = outfile.read_text()
    errors = [line for line in text.splitlines() if line.lstrip().startswith("?")]
    result = {"command": command, "pid": process.pid, "exit_code": process.returncode,
              "wall_seconds": time.monotonic()-start, "sampled_max_rss_bytes": rssmax,
              "child_max_rss_platform_units": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
              "memory_monitor": "ps unavailable in sandbox; only tiny calibrated d4 job run locally",
              "stop_reason": reason, "errors": errors, "input_sha256": sha(path),
              "output_sha256": sha(outfile),
              "completed": "COMPLETE=1" in text and not errors and process.returncode == 0}
    for key in ("INPUT_GENERATORS", "DIMENSION", "QUOTIENT_DIMENSION", "GB_SIZE",
                "GENERATOR_REMAINDERS_ZERO", "UNIT_LIFT_ZERO"):
        match = re.search(r"^"+key+r"=(-?\d+)$", text, re.M)
        if match:
            result[key.lower()] = int(match.group(1))
    return result


def d4_orbits():
    source = OLD / "numerics/e07_exact_d4.py"
    m = load("sz12_d4_exact", source)
    m.check_ring()
    v = m.representative()
    b = tuple(m.conjugate(z) for z in v)

    # This is 2*sigma. sigma fixes sqrt(2),i and sends sqrt(5) to -sqrt(5),
    # r to i*r*(sqrt(5)-1)/2. It is NOT physical complex conjugation.
    irt = m.mul(m.mul(m.I, m.RADICAL), m.sub(m.SQRT5, m.ONE))

    def sigma2(z):
        result = m.ZERO
        for j, coefficient in enumerate(z):
            if not coefficient:
                continue
            term = m.basis(j & 1, (j >> 1) & 1, 0, (j >> 3) & 1)
            term = m.mul(term, irt) if j & 4 else m.scalar(term, 2)
            result = m.add(result, m.scalar(term, coefficient * (-1 if j & 2 else 1)))
        return result

    basis = [m.basis(j & 1, (j >> 1) & 1, (j >> 2) & 1, (j >> 3) & 1)
             for j in range(16)]
    for z in basis:
        assert sigma2(sigma2(z)) == m.scalar(z, 4)
    for z, w in product(basis, repeat=2):
        assert m.mul(sigma2(z), sigma2(w)) == m.scalar(sigma2(m.mul(z, w)), 2)

    ghost = (m.primitive(tuple(sigma2(z) for z in v)),
             m.primitive(tuple(sigma2(z) for z in b)))

    def dot(a, bb):
        result = m.ZERO
        for x, y in zip(a, bb):
            result = m.add(result, m.mul(x, y))
        return result

    def check_pair(a, bb):
        norm = dot(a, bb)
        assert norm != m.ZERO
        nsq = m.mul(norm, norm)
        for k, ell in product(range(4), repeat=2):
            value = m.ZERO
            for j in range(4):
                term = m.mul(m.mul(a[j], bb[(j+k) % 4]),
                             m.mul(bb[(j+ell) % 4], a[(j+k+ell) % 4]))
                value = m.add(value, term)
            assert m.scalar(value, 5) == m.scalar(nsq, int(k == 0)+int(ell == 0))
        for p, q in product(range(4), repeat=2):
            if (p, q) == (0, 0):
                continue
            forward = m.apply_displacement(a, (p, q))
            inverse = tuple(m.phase_i(a[(j+p) % 4], -q*j) for j in range(4))
            assert m.scalar(m.mul(dot(forward, bb), dot(inverse, bb)), 5) == nsq
        witness = None
        for j, k in product(range(4), repeat=2):
            residual = m.sub(m.mul(m.mul(a[j], bb[k]), m.conjugate(norm)),
                             m.mul(m.conjugate(m.mul(a[k], bb[j])), norm))
            if residual != m.ZERO:
                witness = {"indices": [j, k], "residual_basis": list(residual)}
                break
        return {"fourier_equations": 16, "WH_trace_products": 15,
                "norm_basis": list(norm), "nonHermitian_witness": witness}

    group = m.exact_group_images(v)
    output = {"group_order": len(group), "sigma_order": 2, "upstream_sha256": sha(source)}
    output["packets"] = {}
    for label, pair in (("physical", (v, b)), ("ghost", ghost)):
        checks = check_pair(*pair)
        assert (checks["nonHermitian_witness"] is None) == (label == "physical")
        stable = []
        zero_x = zero_y = 0
        for anti in (False, True):
            initial = (pair[1], pair[0]) if anti else pair
            cache = {"": initial}

            def word_image(word):
                if word not in cache:
                    x, y = word_image(word[:-1])
                    ux = m.apply_gate(word[-1], x)
                    uy = tuple(m.conjugate(z) for z in m.apply_gate(
                        word[-1], tuple(m.conjugate(z) for z in y)))
                    cache[word] = (ux, uy)
                return cache[word]

            for key, entry in group.items():
                if entry["anti"] != anti:
                    continue
                x, y = word_image(entry["word"])
                q = entry["q"]
                x = m.apply_displacement(x, q)
                y = tuple(m.conjugate(z) for z in m.apply_displacement(
                    tuple(m.conjugate(z) for z in y), q))
                zero_x += int(x[0] == m.ZERO)
                zero_y += int(y[0] == m.ZERO)
                if m.fixes_ray(pair[0], x) and m.fixes_ray(pair[1], y):
                    stable.append({"key": list(key), "order": m.order(key), "anti": anti})
        assert len(stable) == 6 and zero_x == zero_y == 0
        assert Counter(row["order"] for row in stable) == {1: 1, 2: 1, 3: 2, 6: 2}
        checks.update({"stabilizer": stable, "stabilizer_order": len(stable),
                       "orbit_size": len(group)//len(stable),
                       "zero_first_ket_images": zero_x, "zero_first_bra_images": zero_y})
        output["packets"][label] = checks
        print(f"D4 {label}: 16 quartics, 15 trace products, stabilizer=6, chart points=256", flush=True)
    output["known_distinct_chart_points"] = 512
    output["disjointness"] = "Hermitian property is preserved by all EC maps and inverses"
    return output


def d5_lower():
    source = OLD / "numerics/e09_exact_d5.py"
    m = load("sz12_d5_exact", source)
    field = m.check_field_and_sigma()
    v = m.representative()
    b = tuple(m.conjugate(z) for z in v)
    ghost = (m.primitive(tuple(m.sigma_numerator(z) for z in v)),
             m.primitive(tuple(m.sigma_numerator(z) for z in b)))
    group, sl = m.full_group()
    output = {"group_order": len(group), "field": field, "upstream_sha256": sha(source),
              "input_text_sha256": sha(OLD / "calibration/sg_appendix_b_d4_d7.txt"),
              "packets": {}}
    for label, pair in (("physical", (v, b)), ("ghost", ghost)):
        norm = m.verify_quartics(*pair)
        m.verify_trace_products(*pair, norm)
        witness = m.hermitian_witness(*pair, norm)
        assert (witness is None) == (label == "physical")
        result = m.enumerate_pair_orbit(*pair, group, sl, label)
        result["nonHermitian_witness"] = witness
        output["packets"][label] = result
    output["known_distinct_chart_points"] = 4000
    output["complete_classification"] = False
    return output


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--probe-d5-zero", action="store_true")
    args = parser.parse_args()
    start = time.monotonic()
    (BASE / "data").mkdir(exist_ok=True)
    (BASE / "offline").mkdir(exist_ok=True)
    d4file = BASE / "numerics/e01_d4_trace_one.sing"
    d4file.write_text(emit_singular(4))
    (BASE / "offline/d5_trace_one.sing").write_text(emit_singular(5))
    zerofile = BASE / "offline/d5_zero_ket.sing"
    zerofile.write_text(emit_singular(5, zero_ket=4, lift_unit=True))
    result = {"python": sys.version, "platform": platform.platform(), "seed": SEED,
              "random_choices": 0, "threads": 1, "precision": "exact integers and rationals",
              "script_sha256": sha(Path(__file__))}
    result["d4_upper"] = run_singular(d4file)
    assert result["d4_upper"]["completed"], result["d4_upper"]
    assert result["d4_upper"]["dimension"] == 0
    assert result["d4_upper"]["quotient_dimension"] == 512
    assert result["d4_upper"]["generator_remainders_zero"] == 1
    print("D4 exact QQ chart: dimension=0, quotient length=512", flush=True)
    result["d4"] = d4_orbits()
    result["d4"]["complete_classification"] = True
    result["d5"] = d5_lower()
    if args.probe_d5_zero:
        result["d5_zero_ket_probe"] = {"completed": False,
            "reason": "not run: sandbox denies RSS monitoring; leave uncalibrated job offline"}
        print("D5 zero ket probe:", json.dumps(result["d5_zero_ket_probe"]), flush=True)
    result["support_thresholds"] = {
        "d4": {"support_lower_bound": 3, "free_orbit_chart_lower_bound": 1152,
               "certified_chart_length": 512, "no_free_complex_points": True},
        "d5": {"support_lower_bound": 3, "free_orbit_chart_lower_bound": 3600,
               "known_nonfree_chart_points": 4000, "sufficient_strict_upper_threshold": 7600,
               "no_free_complex_points": "open"}}
    result["wall_seconds"] = time.monotonic()-start
    (BASE / "data/e01_exact_complex_calibration.json").write_text(
        json.dumps(result, ensure_ascii=False, indent=2)+"\n")
    print("PASS: d4 complete 512-point normalized complex variety, two EC stabilizers of order 6", flush=True)
    print("PASS: d5 lower bound 4000 normalized complex points, not a completeness claim", flush=True)
    print("SECONDS", result["wall_seconds"], flush=True)


if __name__ == "__main__":
    main()
