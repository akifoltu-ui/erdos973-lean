#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Lean check for this repository (Python 3 standard library only).

Every main file and every negative control listed in FILES is compiled with `lake env lean`.
  main file         PASS when Lean reports no error and no sorry, and every `#print axioms` line
                    of the file lists only propext, Classical.choice and Quot.sound
  negative control  flagged when Lean reports an error or sorry (sorryAx)
Files of the kinds "recorded" (earlier version) and "auxiliary" are kept as recorded and are not compiled.

Usage:
  python3 scripts/check_lean.py [--project DIR] [--lake PATH] [--timeout SECONDS]
  --project  Lake workspace in which `lake env lean` runs (default: the repository root,
             after `lake exe cache get`)
Exit code 0 when every main file passes and every negative control is flagged.
"""
import argparse
import os
import re
import shutil
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
FILES = [
    ("lean/TURAN973_v04/Turan973_N21.lean", "main"),
    ("lean/TURAN973_v04/Turan973_N31.lean", "main"),
    ("lean/TURAN973_v04/Turan973_N50.lean", "main"),
    ("lean/TURAN973_v04/Turan973_N75.lean", "main"),
    ("lean/TURAN973_v04/Kontrol_N21_bir.lean", "negative"),
    ("lean/TURAN973_v04/Kontrol_N21_ice.lean", "negative"),
    ("lean/TURAN973_v04/Kontrol_N21_sahte.lean", "negative"),
    ("lean/TURAN973_v04/Kontrol_N21_sinir.lean", "negative"),
    ("lean/TURAN973_v05/Turan973_L2_v2.lean", "main"),
    ("lean/TURAN973_v05/Kontrol_L2_v2_sahte.lean", "negative"),
    ("lean/TURAN973_v05/Kontrol_L2_v2_yanlis.lean", "negative"),
    ("lean/TURAN973_v05/Kontrol_L2_sahte.lean", "recorded"),
    ("lean/TURAN973_v05/Kontrol_L2_yanlis.lean", "recorded"),
    ("lean/TURAN973_v05/Turan973_L2.lean", "recorded"),
    ("lean/TURAN973_v05/L2_Sonda.lean", "auxiliary"),
    ("lean/TURAN973_v05/L2_Sonda_v2.lean", "auxiliary"),
    ("lean/TURAN973_v06_r2/Birlesim_N21.lean", "main"),
    ("lean/TURAN973_v06_r2/Birlesim_N31.lean", "main"),
    ("lean/TURAN973_v06_r2/Birlesim_N50.lean", "main"),
    ("lean/TURAN973_v06_r2/Birlesim_N75.lean", "main"),
    ("lean/TURAN973_v06_r2/Kontrol_B21_n22.lean", "negative"),
    ("lean/TURAN973_v06_r2/Kontrol_B21_sahte.lean", "negative"),
    ("lean/TURAN973_v06_r2/Kontrol_B21_sinir.lean", "negative"),
]


def say(s):
    print(str(s).encode("ascii", "backslashreplace").decode("ascii"), flush=True)


def find_lake(arg):
    if arg:
        return arg
    p = shutil.which("lake")
    if p:
        return p
    for name in ("lake.exe", "lake"):
        q = os.path.join(os.path.expanduser("~"), ".elan", "bin", name)
        if os.path.isfile(q):
            return q
    sys.exit("lake not found: install elan (https://github.com/leanprover/elan) or pass --lake PATH")


def axiom_lines(out):
    found = []
    for name, ax in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", out, re.S):
        found.append((name, set(a.strip() for a in ax.replace("\n", " ").split(",") if a.strip())))
    for name in re.findall(r"'([^']+)' does not depend on any axioms", out):
        found.append((name, set()))
    return found


def error_count(out):
    return len(re.findall(r"(?m)(?::\d+:\d+: error\b|^error\b)", out))


def print_axioms_count(path):
    with open(path, encoding="utf-8") as f:
        return sum(1 for line in f if line.lstrip().startswith("#print axioms"))


def judge(kind, code, out, expected):
    errors = error_count(out)
    axioms = axiom_lines(out)
    sorry = "declaration uses 'sorry'" in out or any("sorryAx" in ax for _, ax in axioms)
    if kind == "main":
        bad = sorted(set(a for _, ax in axioms for a in ax) - STANDARD)
        ok = code == 0 and errors == 0 and not sorry and len(axioms) == expected and not bad
        return ok, "exit %s, errors %d, axiom lines %d/%d, axioms %s" % (
            code, errors, len(axioms), expected, "standard" if not bad else ", ".join(bad))
    ok = (code is not None and code != 0) or errors > 0 or sorry
    return ok, "exit %s, errors %d, sorry %s" % (code, errors, "yes" if sorry else "no")


def main():
    ap = argparse.ArgumentParser(description="Lean check for this repository")
    ap.add_argument("--project", default=ROOT)
    ap.add_argument("--lake")
    ap.add_argument("--timeout", type=int, default=7200)
    a = ap.parse_args()
    lake = find_lake(a.lake)
    project = os.path.abspath(a.project)
    say("lake: %s" % lake)
    say("workspace: %s" % project)
    n = {"main": [0, 0], "negative": [0, 0]}
    for rel, kind in FILES:
        path = os.path.join(ROOT, *rel.split("/"))
        if kind not in n:
            say("%-46s %-9s not compiled (kept as recorded)" % (rel, kind))
            continue
        t0 = time.time()
        try:
            p = subprocess.run([lake, "env", "lean", path], cwd=project, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, timeout=a.timeout)
            code, out = p.returncode, p.stdout.decode("utf-8", "replace")
        except subprocess.TimeoutExpired:
            code, out = None, ""
        ok, note = judge(kind, code, out, print_axioms_count(path) if kind == "main" else 0)
        if code is None:
            ok, note = False, "timeout after %d s" % a.timeout
        n[kind][1] += 1
        n[kind][0] += 1 if ok else 0
        status = ("PASS" if ok else "FAIL") if kind == "main" else ("flagged" if ok else "NOT flagged")
        say("%-46s %-9s %-11s %7.1f s  %s" % (rel, kind, status, time.time() - t0, note))
    line = "SUMMARY: %d/%d main files PASS, %d/%d negative controls flagged" % (
        n["main"][0], n["main"][1], n["negative"][0], n["negative"][1])
    say(line)
    good = n["main"][1] > 0 and n["main"][0] == n["main"][1] and n["negative"][0] == n["negative"][1]
    sys.exit(0 if good else 1)


if __name__ == "__main__":
    main()
