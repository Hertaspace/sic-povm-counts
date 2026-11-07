# Certificate attachment

The public [v1.0 release attachment](https://github.com/Hertaspace/sic-povm-counts/releases/download/v1.0/d7-root-certificates.tar.zst), `d7-root-certificates.tar.zst`, contains the 886 frozen root-certificate blocks used by the dimension-seven off-base proof. The archive is 167080642 bytes (about 167 MB). Its SHA-256 is `e047c3d49abad7a4eb07325381d3a326ea93805d96abe1374c357d8ef87b5f57`. Restoration produces 372136711 bytes (about 372 MB) of mathematical payload.

The tag is `v1.0` and the asset name is `d7-root-certificates.tar.zst`. [attachment.json](attachment.json) records the download URL, size, hash, member count, and restored size. Each restored member hash appears in [MANIFEST.md](../MANIFEST.md), [provenance.json](../provenance.json), and the frozen snapshot. The archive uses public relative member names and normalized tar ownership and timestamps. It is distributed as a release asset rather than a tracked repository file.

From the repository root, download, check, and restore it:

```sh
curl -L -o release/d7-root-certificates.tar.zst https://github.com/Hertaspace/sic-povm-counts/releases/download/v1.0/d7-root-certificates.tar.zst
printf '%s\n' 'e047c3d49abad7a4eb07325381d3a326ea93805d96abe1374c357d8ef87b5f57  release/d7-root-certificates.tar.zst' | sha256sum -c -
python -B replay/restore_release.py
python -B replay/run.py integrity
python -B replay/run.py d7-spurious
```

On macOS, replace `sha256sum -c -` with `shasum -a 256 -c -`.

The restore script checks the whole attachment and every member, rejects unexpected paths and links, and refuses to overwrite a differing existing input. It restores `sources/d7/numerics/e41_d7_cert_*.jsonl`. The frozen proof uses exactly these 886 blocks. Restoration and `integrity` verify bytes and record structure. The `d7-spurious` command separately replays root existence, simplicity, freeness, and separation.

The `d4`, `d5`, `d6`, `d7-finiteness`, `d7-faces`, `d7-orbits`, and `ghosts` commands run without this attachment. See the [README replay section](../README.md#replay) and [environment notes](../replay/ENVIRONMENT.md).
