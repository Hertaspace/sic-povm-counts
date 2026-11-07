# Complexified SIC counts in dimensions 4–7

This repository contains computer-aided proofs that the **complexified Weyl–Heisenberg SIC equations have exactly 512, 4000, 6912 and 32928 solutions in dimensions 4, 5, 6 and 7**, together with the proof notes, programs, certificates and replay commands.

- **Counts:** every solution is a reduced point, and exactly half of the solutions are Hermitian (the SIC fiducial projectors).
- **SICs:** the Hermitian solutions are exactly the known orbits 4a, 5a, 6a, 7a and 7b.
- **Strong Zauner:** in dimensions 6 and 7 every solution has ordinary Clifford stabilizer exactly a canonical group of order 3.
- **Ghosts:** every non-Hermitian solution is a displaced-parity ghost, so Khodaiemehr's Conjecture III.1 holds for 4 ≤ d ≤ 7.
- **Type of proof:** computer-aided proofs combined with written arguments, not formalized in a proof assistant (see [Trust boundary](#trust-boundary)).
- **Prior work:** Khodaiemehr reported the counts 512, 4000 and 6912 numerically [Kho26, Table I]. The SIC orbits in these dimensions were known [RBSC04, App05, SG10]. The new part is the certified completeness of the full complexified solution sets, including dimension 7.

## Main result

Let $Xe_j=e_{j+1}$, $Ze_j=\omega^je_j$ with $\omega=e^{2\pi i/d}$, and $D_p=\tau^{p_1p_2}X^{p_1}Z^{p_2}$ with $\tau=-e^{\pi i/d}$ [ACFW18, §2]. Labels are integer pairs with period $d$ for odd $d$ and $2d$ for even $d$, and the equations below depend only on labels modulo $d$. For independent vectors $a,b\in\mathbb C^d$ put $S=b^Ta$ and $\Pi=ab^T/S$. The scheme $Y_d\subset\mathbb P^{d-1}\times\mathbb P^{d-1}$ is defined by $S\ne0$ and

$$(d+1)\,\mathrm{tr}(\Pi D_p)\,\mathrm{tr}(\Pi D_p^\dagger)=1\qquad\text{for all } 0\ne p\in(\mathbb Z/d\mathbb Z)^2.$$

It is the scheme $V_d$ of [Kho26, Definition II.1]. Its Hermitian points ($\Pi=\Pi^\dagger$) are the Weyl–Heisenberg SIC fiducial projectors. No Hermiticity, symmetry or subspace is assumed. Counts are of individual projectors, before any quotient by a group.

The ordinary projective Clifford group consists of the unitary normalizers of the displacement group, modulo phases. The extended Clifford group also contains the antiunitary normalizers. The labels 4a–7b of [SG10] name orbits of the extended group on Hermitian projectors.

**Theorem.** For $d=4,5,6,7$ the scheme $Y_d$ is finite and reduced, with the following points.

| d | Points of $Y_d$ | Hermitian | Non-Hermitian | Hermitian extended orbits [SG10] |
|---|---:|---:|---:|---|
| 4 | 512 | 256 | 256 | 4a |
| 5 | 4000 | 2000 | 2000 | 5a |
| 6 | 6912 | 3456 | 3456 | 6a |
| 7 | 32928 | 16464 | 16464 | 7a (10976), 7b (5488) |

$Y_6$ consists of four ordinary Clifford orbits of 1728 points and $Y_7$ of six ordinary orbits of 5488 points. In both, every point has ordinary projective Clifford stabilizer exactly a canonical order-3 group, meaning that its nonidentity elements have symplectic matrices of trace $-1 \bmod d$ [App05, §5]. Appleby's Conjecture A [App05, §6], the strong Zauner conjecture, therefore holds in dimensions 6 and 7.

The Hermitian counts agree with the orbit sizes of Scott and Grassl [SG10, Table I]: $16\cdot4^2$, $80\cdot5^2$, $96\cdot6^2$ and $336\cdot7^2$.

## How the counts are proved

The upper bound comes from a multihomogeneous Bézout count $B_d$ of a perturbed square system, once finiteness is known. Paths ending on the boundary ($C$) or at spurious roots ($N$) are subtracted, so $|Y_d|\le B_d-C-N$. Exact solutions give the lower bound.

For $d=4,5,6$ the computations use special fibres at a prime dividing $d+1$. Write $Z_p=b^TD_pa$ and let $t$ be the common value of $Z_pZ_{-p}$ for $p\ne0$, so that $S^2=(d+1)t$. The special fibres are those of the integral model with $t$ invertible. At these primes every special point has $S=0$, so escape means degeneration to $t=0$, not to $S=0$.

- **d = 4.** $1280=512+768+0$. The boundary contribution 768 and the special fibre at 5 (length 512) are computed exactly. Two exact 256-point orbits attain the bound. [PROOFS/d4.md](PROOFS/d4.md)
- **d = 5.** A support census, 59 unit identities and valuation-cell coverage exclude escape at 3. The fibre at 3 has length 4000, and two exact 2000-point orbits attain it. [PROOFS/d5.md](PROOFS/d5.md)
- **d = 6.** Escape is excluded at 7. Each of the 3456 points of the fibre at 7 has local algebra of length two and lifts to exactly two reduced complex points. [PROOFS/d6.md](PROOFS/d6.md)
- **d = 7.** Finiteness is proved at 29 over all 544 boundary supports. Then $3784704=32928+1671040+2080736$: face systems give at least 1671040 boundary paths, interval certificates give at least 2080736 spurious roots, and six exact Clifford orbits give 32928 points. [PROOFS/d7.md](PROOFS/d7.md)
- **Ghosts.** A deduction from these classifications, using ghost existence [AFK26, Thm. 1.3] in dimensions 4–6 and explicit checks in dimension 7. [PROOFS/ghosts.md](PROOFS/ghosts.md)

## Verification

### Replay

Install Python 3.14 and the pins in [requirements.txt](requirements.txt), plus Singular, msolve, PARI/GP, Z3 and a C++17 compiler, as described in [replay/ENVIRONMENT.md](replay/ENVIRONMENT.md). Do not use optimized Python (`-O`). Each claim runs in a fresh copy of the repository, checks explicit acceptance fields and writes a `result.json` that binds the source, inputs and outputs by SHA-256.

```sh
python -B replay/run.py d4             # also d5, d6, d7-finiteness, d7-faces, d7-orbits, ghosts
```

`d7-spurious` and `integrity` need the release attachment (167080642 bytes, 886 certificate blocks):

```sh
curl -L -o release/d7-root-certificates.tar.zst \
  https://github.com/Hertaspace/sic-povm-counts/releases/download/v1.0/d7-root-certificates.tar.zst
echo 'e047c3d49abad7a4eb07325381d3a326ea93805d96abe1374c357d8ef87b5f57  release/d7-root-certificates.tar.zst' | sha256sum -c -
python -B replay/restore_release.py
python -B replay/run.py integrity
python -B replay/run.py d7-spurious
```

On macOS use `shasum -a 256 -c -`. `python -B replay/run.py <claim> --records-only` inspects the saved historical records without recomputing.

### Results

All nine subcommands passed in a clean Linux environment (AMD EPYC 7763) on 6 November 2026. The records are in [replay/clean-run/](replay/clean-run/), and [replay/VALIDATION.md](replay/VALIDATION.md) describes the run.

| Claim | Command | What a PASS checks | Wall time | Peak memory |
|---|---|---|---:|---:|
| d = 4 | `d4` | special fibre 512, boundary 768, exact 512-point lower bound | 1 min 47 s | 65 MiB |
| d = 5 | `d5` | fibre 4000, support and cell exclusions, two exact orbits | 7 min 20 s | 289 MiB |
| d = 6 | `d6` | fibre, fresh covers, local and group checks, exact seeds | 14 min 33 s | 2.8 GiB |
| d = 7 finiteness | `d7-finiteness` | 544-support census, 25 identities, all weight covers UNSAT | 37 min 37 s | 1.06 GiB |
| d = 7 boundary | `d7-faces` | 48 face groups, $C\ge1671040$ | 16 min 59 s | 1.12 GiB |
| d = 7 spurious roots | `d7-spurious` | 886 blocks, root existence, simplicity and separation, $N\ge2080736$ | 1 h 21 min | 135 MiB per process |
| d = 7 orbits | `d7-orbits` | exact seeds, six orbits, stabilizers, links to 7a and 7b | 1 min 38 s | 159 MiB |
| ghosts | `ghosts` | saved classification dependencies and branch arithmetic | 6 s | 29 MiB |
| integrity | `integrity` | inventory hashes and restored blocks (no mathematics) | 8 s | 30 MiB |

Peak memory is the largest single process reported by `/usr/bin/time`. The four d = 7 components and the counting argument are needed together. One of them alone does not prove the count.

### Trust boundary

- The written arguments in [PROOFS/](PROOFS/): specialization, local algebras, lifting, intersection counts and parity.
- Exact arithmetic in the source programs, Singular and msolve quotient lengths, and PARI/GP irreducibility checks.
- Z3 UNSAT answers, trusted without independently checked proof objects, and the completeness of the encoded support and valuation models. In d = 5 the saved final SMT systems rely on the exposed generators that produced them ([PROOFS/d5.md](PROOFS/d5.md)).
- The outward-rounded interval code used for the spurious roots, checked by two separate implementations.

Numerical solving only supplied candidates. Nothing here is formalized in a proof assistant.

## Repository layout

| Path | Contents |
|---|---|
| `PROOFS/` | step-by-step proof notes and acceptance conditions for each dimension and for the ghost statement |
| `replay/` | unified runner `run.py`, acceptance checks, environment and validation notes, clean-replay records |
| `sources/` | primary programs, certificates and original computational records, by dimension and topic |
| `independent/` | separate implementations used to cross-check the d = 7 finiteness, faces, spurious roots and orbits |
| `release/` | metadata and instructions for the certificate attachment |
| `MANIFEST.md`, `provenance.json`, `SHA256SUMS` | file inventory, original and published hashes, checksums |

File prefixes such as `e10` are local experiment labels, so the same prefix can occur in different directories. Historical `PASS` fields in imported records describe the original runs. The fresh replays above write their own records.

## Sources

- [ACFW18] M. Appleby, T.-Y. Chien, S. Flammia, S. Waldron, *Constructing exact symmetric informationally complete measurements from numerical solutions*, J. Phys. A 51 (2018) 165302, [arXiv:1703.05981](https://arxiv.org/abs/1703.05981).
- [AFK26] M. Appleby, S. T. Flammia, G. S. Kopp, *The twisted convolution identity and ghost r-SICs from finite quantum dilogarithms*, [arXiv:2609.39192](https://arxiv.org/abs/2609.39192).
- [App05] D. M. Appleby, *SIC-POVMs and the extended Clifford group*, J. Math. Phys. 46 (2005) 052107, [arXiv:quant-ph/0412001](https://arxiv.org/abs/quant-ph/0412001).
- [Kho26] H. Khodaiemehr, *From ghost SICs to SIC-POVMs: a Galois reduction of Zauner's conjecture*, [arXiv:2611.01524](https://arxiv.org/abs/2611.01524).
- [RBSC04] J. M. Renes, R. Blume-Kohout, A. J. Scott, C. M. Caves, *Symmetric informationally complete quantum measurements*, J. Math. Phys. 45 (2004) 2171, [arXiv:quant-ph/0310075](https://arxiv.org/abs/quant-ph/0310075).
- [SG10] A. J. Scott, M. Grassl, *SIC-POVMs: a new computer study*, J. Math. Phys. 51 (2010) 042203, [arXiv:0910.5784](https://arxiv.org/abs/0910.5784).

## How this work was produced

The arguments, code and evidence were developed under human direction by large language model agents, and agents from different providers cross-checked parts of them. Independent verification is welcome. If you find a problem, please [open an issue](https://github.com/Hertaspace/sic-povm-counts/issues) with the claim, command, environment and relevant output.

## License

Code is under the [MIT License](LICENSE), including Python, C++, PARI/GP, Singular and SMT-LIB sources. Documentation and data, including proof notes, certificates and recorded outputs, are under [CC BY 4.0](LICENSE-DATA). Third-party material keeps its attribution.

## Citation

```bibtex
@misc{yang2026siccounts,
  author       = {Yang, Yaoling},
  title        = {Computer-aided counts of complexified {SIC} solutions in dimensions four through seven},
  year         = {2026},
  howpublished = {GitHub repository},
  url          = {https://github.com/Hertaspace/sic-povm-counts},
  note         = {Release v1.0}
}
```
