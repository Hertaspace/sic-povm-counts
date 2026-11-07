# Publication-build checks and clean replay

Author: Yaoling Yang. Date: 6 November 2026.

This record separates the checks used to assemble the publication build from the clean replay of the computational claims. Every unified subcommand passed in the clean Linux environment. The seven computational claims regenerated outputs in fresh-execution mode. The `ghosts` and `integrity` subcommands retain their documented scope as record and byte checks. Returned `result.json` files, source/input/output bindings, and regenerated stage reports are included under `replay/clean-run/`.

## 1. Publication-build checks

### Imported bytes and metadata

All 1525 selected original files were present and matched their selected original SHA-256, including the three recovered dimension-seven root/separation reports. Of these, 1433 retained identical bytes and 92 were adapted. Across the 25 edited JSON files, all **166641 numeric, boolean, and null values** were compared with the originals and remained equal. Changes were to path keys and 296 metadata string values. All 38 compressed multipart pieces and all 886 frozen root blocks retained their original bytes. Polynomial and certificate payloads were not rewritten.

The publication build recorded source correspondence in `provenance.json`, `SHA256SUMS`, and `replay/bindings.json`. The latter records 5017 links from historical digest references to published bytes. Its scope is byte correspondence. Historical success fields describe their original executions. The dimension-six runner binds the newly captured exact-orbit output, and the outer runner binds the full 291-file selected input closure.

The release attachment was decompressed and every one of its 886 members checked against the frozen snapshot. Its whole-archive hash and exact byte count appear in [release/attachment.json](../release/attachment.json). Restoration verified input integrity. Root certification was separately replayed in the clean run below.

### Lightweight computations and acceptance checks

The publication-build outputs and input/source bindings are in [local/validation.json](local/validation.json) and the adjacent output files. Small standard-library runs used Python 3.15.0. Symbolic model checks used Python 3.14.7 with SymPy 1.14.0. These checks had the following scopes:

- The exact dimension-four Hermitian seed check found 256 distinct rays, extended group order 1536, and stabilizer order 6. This checked one orbit.
- The exact dimension-five lower bound checked two disjoint 2000-point orbits, a degree-32 field, group order 6000, and all seed equations.
- The integer-interval self-test checked 32000 exact endpoints and 1563 signed-pair equation/Jacobian comparisons.
- Corrupted interval inputs were rejected: a shifted center, zero inverse, zero freeness witnesses, invalid equation witness, shifted root of unity, and changed matrix numerator.
- PARI/GP verified field-tower degrees `4,8,48` and irreducibility.
- The exact equation-space basis check accepted rank 15, all 2688 spanning identities, and the nonzero rank witness.
- The off-base symmetry check accepted 98 projective normal forms, all 9604 multiplication pairs, and exact equation invariance.
- The independent finiteness model self-test checked the literal Weyl reconstruction, 441 rank-one minors, 49 square equations, and parser/trace tests.

Every Python source parsed successfully. The support-census C++ source passed C++17 syntax checking. The finiteness identity audit verified all 25 identities over $\mathbb F_{29}$. Exact Gaussian elimination explained all 125 unmatched linear generators as block relations. Every identity records `unmatched_linear_in_block_span=5` and `unmatched_not_explained=[]`. The four circuits authenticate their complete dependencies, including 87 character-projection leaves. Integer grading differences from valuation weights remain diagnostic.

```sh
python -B replay/test_acceptance.py
```

All **20** acceptance tests passed in the publication-build checks. They reject overlapping orbits, duplicate reference labels, false seed identities, a wrong displacement kernel, a missing non-Hermitian witness, a corrupted frozen block, a consistently falsified face weight, optimized Python, and a historical dimension-six report presented as fresh. They accept the original three-face records as 12 groups and reject them when offered as the full 48-group result. The finiteness regressions accept explained block relations and reject unexplained, altered, nonlinear, incompletely counted, or unsampled used generators. They also reject a weight-cover result that is not UNSAT. The bounded timeout test stops its recorded child and descendant by exact PID. These tests do not invoke the full computer algebra, SMT, or root pipelines.

Earlier `--records-only` invocations checked saved evidence and isolated-copy bindings. They did not establish fresh computational acceptance. The clean replay below supplies that separate evidence for every computational subcommand.

## 2. Clean replay

The clean run used Linux x86_64 and an AMD EPYC 7763<!-- clean-run -->. The complete observed versions, including Python, Singular, msolve, PARI/GP, Z3, Python packages, compiler, and zstd, are recorded in [ENVIRONMENT.md](ENVIRONMENT.md). PARI/GP 2.17.3<!-- clean-run --> replaced the historical 2.17.4, which is not packaged on conda-forge. No accepted field changed. msolve was built from upstream source.

The [README results table](../README.md#results) records the measured wall times and peak memory. Peak RSS is the largest single process reported by `/usr/bin/time`, not the aggregate across workers. The dimension-seven spurious-root run used four<!-- clean-run --> workers plus the independent checker. The record checks `ghosts` and `integrity` took 6 and 8 seconds with about 30 MiB.

All of the following passed in normal runner mode:

- `python -B replay/run.py d4`: complete special-fibre and boundary lengths and the exact 512-point lower bound.
- `python -B replay/run.py d5`: complete 4000-length fibre, 2000-point coverage, support/cell exclusions, and both exact lower-bound orbits.
- `python -B replay/run.py d6`: recomputed upper bound, all six fresh covers and 147 identities, local and group checks, and exact seeds.
- `python -B replay/run.py d7-finiteness`: all five independent stage reports generated and accepted, including the full support census, identity audit, and complete weight covers.
- `python -B replay/run.py d7-faces`: all 48 groups regenerated and accepted. Detailed outputs now cover all twelve weights, including the nine cones formerly represented only by a historical summary.
- `python -B replay/run.py d7-spurious`: the complete frozen snapshot, root existence and simplicity, freeness witnesses, separation, and outer bindings accepted.
- `python -B replay/run.py d7-orbits`: exact field and seed checks, both modular group passes, full stabilizers, and exact reference-orbit connections accepted.
- `python -B replay/run.py ghosts`: saved classification dependencies and branch arithmetic accepted. The parity and coverage arguments remain written mathematical deductions.
- `python -B replay/run.py integrity`: publication inventory, restored blocks, and record structure accepted.

The finiteness reports and the detailed reports for all 48 face groups are included under `replay/clean-run/`, together with the returned `result.json` files. The original reports remain identifiable as historical evidence.

### Runner corrections recorded during the clean replay

Two runner defects were found and corrected before the successful replay:

- The Linux child-process RSS sampler treated an exiting child without a `VmRSS` line as an error. A missing line for an exiting child now reads as zero.
- The finiteness acceptance gate required zero unmatched generators. The five unmatched generators per identity are linear block relations. Their membership in the block span is now verified by recorded exact Gaussian elimination over $\mathbb F_{29}$, with every unexplained list required to be empty.

The finiteness stage's per-query solver limit was raised to 1<!-- clean-run --> h because the hardest weight cover needed about 210 s historically. It needed 644<!-- clean-run --> s in the clean replay on a shared machine. All eleven cover queries returned UNSAT.

## Scope of the evidence

Fresh execution records computational acceptance for the bound source and input bytes. It does not replace the written specialization, no-escape, local-algebra, lifting, intersection, or parity arguments. The dimension-five saved-final-SMT provenance boundary remains explicit in [PROOFS/d5.md](../PROOFS/d5.md). Z3 UNSAT answers are trusted without independently checked proof objects. The exact arithmetic, computer algebra systems, interval code, and completeness of the encoded models remain part of the declared trust boundary.
