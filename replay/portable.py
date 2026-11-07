"""Repository-relative inputs, PATH tools, and owned-child RSS sampling."""
from __future__ import annotations

import ctypes
import os
from pathlib import Path
import shutil
import sys


def public_root(anchor):
    for parent in Path(anchor).resolve().parents:
        if (parent / "replay" / "portable.py").is_file():
            return parent
    raise RuntimeError("cannot find the public evidence root")


def executable(name):
    key = {"c++": "CXX", "gp": "SIC_GP", "Singular": "SIC_SINGULAR",
           "msolve": "SIC_MSOLVE"}.get(name, "SIC_" + name.upper())
    requested = os.environ.get(key, name)
    found = shutil.which(requested)
    if found is None:
        raise FileNotFoundError("install " + name + " on PATH or set " + key)
    return found


def resident_bytes(pid):
    """Sample one child; return zero only if it has already exited."""
    if sys.platform.startswith("linux"):
        try:
            status = Path(f"/proc/{int(pid)}/status").read_text().splitlines()
            for line in status:
                if line.startswith("VmRSS:"):
                    return int(line.split()[1]) * 1024
        except FileNotFoundError:
            return 0
        # No VmRSS line: the child has released its address space while
        # exiting (or is already a zombie), so it holds no resident memory.
        return 0
    if sys.platform == "darwin":
        lib = ctypes.CDLL("/usr/lib/libproc.dylib", use_errno=True)
        buffer = (ctypes.c_uint64 * 64)()
        if lib.proc_pid_rusage(int(pid), 2, ctypes.byref(buffer)) == 0:
            return int(buffer[8])
        if not _process_exists(pid):
            return 0
        raise OSError(ctypes.get_errno(), "cannot sample owned child RSS")
    raise RuntimeError("RSS monitoring requires Linux or macOS")


def _process_exists(pid):
    try:
        os.kill(int(pid), 0)
        return True
    except ProcessLookupError:
        return False
