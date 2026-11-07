#!/usr/bin/env python3.14
"""Exact arithmetic only. Never promotes the supplied numerical spur count."""

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
import json
import math
import platform
from pathlib import Path

SEED = 20261102


def main():
    bezout = 2**12 * math.comb(12, 6)
    supplied = {"q": [1000, 1968, 576, 640], "z": [96],
                "x1": [8], "x2": [32], "l1": [48, 72], "l2": [48]}
    multiplicities = {"q": 3, "z": 3, "x1": 2, "x2": 6,
                      "l1": 6, "l2": 6}
    units = sum(multiplicities[k] * sum(v) for k, v in supplied.items())
    spur_numerical = 98 * 21232
    bound_conditional = bezout - spur_numerical - 112 * units
    threshold = 32928 + 16464
    additional_units = (bound_conditional - threshold) // 112 + 1
    closing_units = (bezout - spur_numerical - 32928) // 112
    result = dict(seed=SEED, python=platform.python_version(),
                  nature="exact arithmetic on supplied unverified numerical inputs",
                  bezout=bezout, supplied_counts=supplied,
                  units_multiplicity=multiplicities, supplied_units=units,
                  supplied_spur_numerical=spur_numerical,
                  conditional_bound=bound_conditional,
                  strict_threshold=threshold,
                  least_additional_integer_units=additional_units,
                  strict_bound_at_least_additional=bound_conditional-112*additional_units,
                  target_closure_units=closing_units,
                  missing_closure_units=closing_units-units,
                  calibration_d4=48*16,
                  calibration_d5=120*(64+36)+240*8,
                  calibration_d6=288*256+288*32+24*1920,
                  no_new_cones=True, no_certified_spur_count=True)
    assert result["calibration_d6"] == 129024
    assert bezout == 3784704 and units == 14056
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
