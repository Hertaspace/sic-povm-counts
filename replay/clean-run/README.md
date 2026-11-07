# Clean replay records of 6 November 2026

This directory holds the records returned by the clean replay of every subcommand. All nine subcommands passed with exit code 0.

## Run

- Machine: Linux x86_64, AMD EPYC 7763, jobs pinned to 96 logical CPUs at reduced priority. The machine was shared with unrelated jobs, so wall times are upper estimates.
- Environment: a fresh conda-forge environment with the versions listed in [ENVIRONMENT.md](../ENVIRONMENT.md), plus msolve 0.11.0 built from upstream source.
- Interpreter flags: `PYTHONDONTWRITEBYTECODE=1`, `OMP_NUM_THREADS=1`, `OPENBLAS_NUM_THREADS=1`, never optimized Python.
- Commands, each wrapped in GNU `/usr/bin/time -v`:

```sh
python -B replay/run.py integrity     --run-dir work/final-integrity
python -B replay/run.py d7-orbits     --run-dir work/final-d7-orbits     --timeout 7200
python -B replay/run.py d4            --run-dir work/final-d4            --timeout 7200
python -B replay/run.py d5            --run-dir work/final-d5            --timeout 14400
python -B replay/run.py d6            --run-dir work/final-d6            --timeout 7200
python -B replay/run.py d7-finiteness --run-dir work/final-d7-finiteness --timeout 14400 --threads 2
python -B replay/run.py d7-faces      --run-dir work/final-d7-faces      --timeout 43200 --threads 2
python -B replay/run.py d7-spurious   --run-dir work/final-d7-spurious   --timeout 43200
python -B replay/run.py ghosts        --run-dir work/final-ghosts
```

The first command ran alone, the next seven ran concurrently, and `ghosts` ran last.

## Contents

- [summary.json](summary.json): status, exit code, wall time, peak memory and tree hash for each subcommand.
- [exits.txt](exits.txt): exit codes in completion order.
- `<claim>/result.json`: the runner's record. It binds the source tree, every input and every output by SHA-256.
- `<claim>/logs/`: the logs named in the record's `outputs` list.
- `<claim>/stage-reports/`: regenerated stage reports, recorded in `result.json` under the prefix `work/`. These are the five finiteness reports, the 48-group face reports with `summary.json`, and the exact-orbit summary.
- `<claim>/regenerated/sources/`: outputs that the replay removed and regenerated in its own copy of `sources/`, under the same relative paths. Compare them with the historical files of the same name.
- `<claim>/console.log` and `<claim>/time.txt`: runner console output and the GNU `time` report.

Files larger than 500 KiB are stored gzip-compressed (`.gz`). Decompress them before comparing hashes. Absolute paths in the logs show the workspace prefix `/home/ubuntu/counts-replay` of the replay environment. The records are not normalized, so their bytes match the recorded hashes.

Some outputs bound in `result.json` are not copied here: the 240 msolve intermediate files of the face replay, the 887 per-block reports of the spurious-root replay, two compiled support-census binaries and one process-ID file. Re-running the subcommand regenerates them, and their hashes are in the record.

## Relation to the published tree

All nine records carry the same source-tree hash, `80cd8d86666285eecba5de16c11f192dfa489e4686430bf7e7d618a24fca538d`, over 1561 files. [tree-diff.json](tree-diff.json) compares every recorded input hash with the published tree. Every program, source input and certificate is byte-identical. The only differences are documentation, the license files, the comment line of `requirements.txt`, the attachment metadata (which gained its download URL, with the checksum unchanged), the seal indexes rebuilt after those edits, and this directory.

To check the records against the published tree, restore the release attachment first (see the main README), then run:

```sh
python3 replay/clean-run/compare_tree.py
```
