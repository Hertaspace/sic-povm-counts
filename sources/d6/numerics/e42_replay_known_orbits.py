#!/usr/bin/env python3
"""Replay the exact 6a/Galois-mate algebraic input without historical writes.
The imported entry point prints its certificate and invokes only PARI/GP.
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
sys.dont_write_bytecode=True
from pathlib import Path
import importlib.util,os
H=Path(__file__).resolve().parent
os.environ['TMPDIR']=str(H)
path=public_root(__file__)/'sources/prime-fibres/numerics'/'e32_d6_norms.py'
spec=importlib.util.spec_from_file_location('e42_readonly_known_orbits',path)
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
if __name__=='__main__':module.main()
