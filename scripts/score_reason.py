#!/usr/bin/env python
"""score_reason.py — run HermiT DL reasoning over the SCORE ontologies.

The deeper companion to score_check.py's structural `owl` check: this runs an actual
description-logic reasoner (HermiT, bundled with owlready2) to verify
  (1) score-core.owl is consistent on its own, and
  (2) core + polaris is consistent — the refinement-conformance contract
      (no implementation axiom contradicts a core axiom; no class unsatisfiable).

Needs a JRE. None is on PATH, but Protégé bundles one; this script auto-detects it
(or honour JAVA_EXE / a --java override). Install dep: pip install owlready2.

Run: .venv/Scripts/python.exe scripts/score_reason.py
Exit 0 if both ontologies consistent with no unsatisfiable classes; 1 otherwise.
"""
from __future__ import annotations

import argparse
import glob
import os
import sys
from pathlib import Path

import owlready2
from owlready2 import World, sync_reasoner_hermit
from owlready2.base import OwlReadyInconsistentOntologyError

ROOT = Path(__file__).resolve().parent.parent
FORMAL = ROOT / "formal"
CORE = ("http://score-theory.org/core", FORMAL / "score-core.owl")


def impl_ontologies() -> list[tuple[str, Path]]:
    """Auto-discover all score-<impl>.owl files in formal/ (excluding core)."""
    impls = []
    for p in sorted(FORMAL.glob("score-*.owl")):
        if p.name == "score-core.owl":
            continue
        # derive IRI from filename: score-polaris.owl -> http://score-theory.org/polaris
        name = p.stem.replace("score-", "")   # "polaris", "ethos", ...
        iri = f"http://score-theory.org/{name}"
        impls.append((iri, p))
    return impls


def find_java() -> str | None:
    if os.environ.get("JAVA_EXE") and Path(os.environ["JAVA_EXE"]).exists():
        return os.environ["JAVA_EXE"]
    import shutil
    if shutil.which("java"):
        return shutil.which("java")
    # Protégé bundles a JRE
    for pat in (r"C:\Program Files\Protege-*\jre\bin\java.exe",
                r"C:\Program Files (x86)\Protege-*\jre\bin\java.exe"):
        hits = sorted(glob.glob(pat))
        if hits:
            return hits[-1]
    return None


def reason(label: str, onts: list[tuple[str, Path]]) -> bool:
    """Load (iri, path) ontologies into a fresh world and run HermiT. Return True if
    consistent. Loading under each ontology's real IRI lets owl:imports resolve to the
    already-loaded core; loading via fileobj avoids Windows file:// path mangling."""
    w = World()
    for iri, path in onts:
        with open(path, "rb") as fh:
            w.get_ontology(iri).load(fileobj=fh)
    print(f"\n=== {label} ===")
    print("  loaded: " + ", ".join(p.name for _, p in onts))
    try:
        sync_reasoner_hermit(w, infer_property_values=False)
    except OwlReadyInconsistentOntologyError:
        print("  RESULT: INCONSISTENT (HermiT)")
        return False
    unsat = [c for c in w.inconsistent_classes() if c is not owlready2.Nothing]
    if unsat:
        print(f"  RESULT: consistent but {len(unsat)} UNSATISFIABLE class(es):")
        for c in unsat:
            print(f"    - {c.iri}")
        return False
    print("  RESULT: consistent; no unsatisfiable classes")
    return True


def main() -> int:
    ap = argparse.ArgumentParser(description="HermiT DL reasoning over SCORE ontologies")
    ap.add_argument("--java", help="path to java.exe (else autodetect: JAVA_EXE, PATH, Protégé JRE)")
    args = ap.parse_args()

    java = args.java or find_java()
    if not java:
        print("ERROR: no JRE found (set JAVA_EXE or install Protégé / a JDK).")
        return 2
    owlready2.JAVA_EXE = java
    print(f"java: {java}")

    impls = impl_ontologies()
    ok_core = reason("score-core.owl (alone)", [CORE])
    results = {"core": ok_core}
    for iri, path in impls:
        name = path.stem  # e.g. "score-polaris"
        ok = reason(f"core + {name} (refinement conformance)", [CORE, (iri, path)])
        results[name] = ok

    summary = " | ".join(f"{k}={'OK' if v else 'FAIL'}" for k, v in results.items())
    print(f"\nsummary: {summary}")
    return 0 if all(results.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
