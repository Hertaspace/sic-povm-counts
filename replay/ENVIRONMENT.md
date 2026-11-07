# Reproduction environment

The clean replay of 6 November 2026 ran on Linux x86_64 with an AMD EPYC 7763<!-- clean-run -->. Every subcommand passed. The computational claims used fresh execution. The `ghosts` and `integrity` subcommands perform record and byte checks. Returned `result.json` files and stage reports are included under `replay/clean-run/`. See [VALIDATION.md](VALIDATION.md) for the distinction between publication-build checks and the clean replay.

## Clean replay versions

- Python 3.14.10<!-- clean-run --> from conda-forge.
- Singular 4.4.1<!-- clean-run --> and PARI/GP 2.17.3<!-- clean-run -->.
- msolve 0.11.0<!-- clean-run --> built from upstream source.
- Z3 5.0.0<!-- clean-run -->, python-flint 0.9.0<!-- clean-run -->, and gmpy2 2.3.2<!-- clean-run --> from pip.
- SymPy 1.14.0<!-- clean-run -->, NumPy 2.5.4<!-- clean-run -->, and SciPy 1.18.1<!-- clean-run --> from pip.
- C++ compiler: conda-forge GCC 15.3.0<!-- clean-run -->, used for the C++17 support-census programs.
- zstd 1.5.7<!-- clean-run --> for the release attachment.

The historical runs used Python 3.14.7 for the dimension-six symbolic replay and 3.14.8 for the dimension-seven interval checks. Historical PARI/GP was 2.17.4. That version is not packaged on conda-forge, so the clean replay used 2.17.3<!-- clean-run -->. No accepted field changed with this version difference. Historical Singular, msolve, Z3, python-flint, and gmpy2 versions agree with the clean versions above.

The earlier publication-build checks used Python 3.15.0 for standard-library checks and Python 3.14.7 with SymPy 1.14.0 for small symbolic checks. They were partial checks. The clean replay tested the combined computational environment listed above.

## Installation and commands

Use Python 3.14 and the package pins in [requirements.txt](../requirements.txt). Do not use `-O`, `-OO`, or `PYTHONOPTIMIZE`. The inherited checkers use assertions, and the public entry points reject optimization. NumPy and SciPy support supplementary sparse-volume proposals. The principal independent face and exact orbit checkers do not need them.

```sh
python3.14 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
Singular --version
msolve --version
gp --version
c++ --version
python -B replay/run.py d4
```

Install the three computer algebra systems and `zstd` using available packages or upstream builds. The clean replay built msolve from upstream source. Executables are discovered on `PATH`. `CXX` selects a C++ compiler. `SIC_SINGULAR`, `SIC_MSOLVE`, and `SIC_GP` select explicit executable paths in the adapted helpers. Some inherited subprocess calls use executable names directly, so put custom wrappers on `PATH` too. No external dependency source or virtual environment is included in the repository.

The seven commands that do not need the attachment are listed in the [README](../README.md#replay). Before `integrity` or `d7-spurious`, follow the [attachment download and checksum instructions](../release/README.md), then run from the repository root:

```sh
python -B replay/restore_release.py
python -B replay/run.py integrity
python -B replay/run.py d7-spurious
```

The unified entry point creates an isolated workspace and binds the actual inputs, source bytes, output bytes, and checked acceptance fields in `result.json`. Raw inherited scripts usually write beside themselves, so execute them only inside a disposable replay copy. `--records-only` inspects saved records without rerunning the underlying computation. Integrity checks establish bytes and record structure.

## Resources and trust

The [README results table](../README.md#results) records full-subcommand wall times and measured peak resident set size (RSS). The RSS values come from `/usr/bin/time` and describe the largest single process, not the aggregate memory of its process tree. The primary dimension-seven interval replay used four<!-- clean-run --> workers plus the independent checker. The record checks `ghosts` and `integrity` took 6 and 8 seconds with about 30 MiB. Historical resource limits are configured ceilings unless explicitly labeled as measured peaks.

The finiteness replay gives each solver query up to 1<!-- clean-run --> h. The hardest weight cover needed about 210 s historically and 644<!-- clean-run --> s in the clean replay on a shared machine. It generated and accepted all five independent stage reports. The face replay regenerated and accepted all 48 groups. Both sets of reports are included under `replay/clean-run/`.

Linux and macOS are supported by the child-process RSS helper. Run large jobs separately when memory is limited. The frozen interval replay does not require numerical root discovery, network access, or an additional data archive once the public attachment has been restored.

SHA-256 identifies inputs. It does not verify mathematical claims. Z3 UNSAT answers are trusted without independently verified solver proof objects. The computer algebra systems, exact arithmetic, interval implementations, and written mathematical arguments remain part of the trust boundary. No proof-assistant formalization is supplied.
