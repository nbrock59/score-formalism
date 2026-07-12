#!/usr/bin/env python
"""score_slots.py --- cross-peer filler inventory for the SCORE core slots (Gate 6).

The mechanical backbone of the cross-peer measurement reconciliation. For every core
class / object property, it reports which implementation layers SPECIALIZE it (a named
rdfs:subClassOf / rdfs:subPropertyOf edge into core), and classifies each core construct by
peer breadth:

  SHARED   (>=2 peers)  -- a consensus-eligible construct; the >=2-peer intersection is the
                           promotion justification. These are where cross-peer agreement is
                           *claimed* and must be semantically audited (DL-consistency does not
                           check that two fillers mean the same thing).
  LOCAL    (1 peer)     -- filled by a single peer so far; either genuinely domain-specific or
                           a latent SHARED awaiting a second peer.
  UNFILLED (0 peers)    -- a core slot no peer has specialized yet.

Stdlib only. Run: .venv/Scripts/python.exe scripts/score_slots.py [--measurement]
`--measurement` restricts the report to the measurement/fitness/operator slots.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

try:
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
except (AttributeError, ValueError):
    pass

ROOT = Path(__file__).resolve().parent.parent
FORMAL = ROOT / "formal"

# The core constructs most relevant to the consensus-metric question.
MEASUREMENT_SLOTS = {
    "MeasurementModel", "FitnessCriterion", "AdjacentPossibleMeasure",
    "CollectiveManifoldUpdate", "PathologicalAttractor",
    "InterventionClass", "SigmaInterventionClass",
    "DoctrinalRegion", "doctrinallyComposesFrom",
    "SpectralEarlyWarningIndicator",
    "Trace", "TraceProcessor", "TimeDomainProcessor", "TransformDomainProcessor",
}


def impl_of(path: Path) -> str:
    return path.stem.replace("score-", "")


def parse(path: Path) -> list[tuple[str, str]]:
    """Return (child, namedParent) edges for classes and object properties in one OWL file.
    Only *named*-superclass edges (rdfs:subClassOf/subPropertyOf rdf:resource=...#Name); the
    anonymous Restriction subClassOf axioms are skipped (they carry no consensus signal)."""
    txt = path.read_text(encoding="utf-8")
    edges: list[tuple[str, str]] = []
    # split into per-entity blocks on Class/ObjectProperty declarations
    blocks = re.split(r'(?=<owl:(?:Class|ObjectProperty)\s+rdf:about=)', txt)
    for b in blocks:
        m = re.match(r'<owl:(?:Class|ObjectProperty)\s+rdf:about="[^"]*#([A-Za-z0-9_]+)"', b)
        if not m:
            continue
        child = m.group(1)
        for pm in re.finditer(r'<rdfs:sub(?:ClassOf|PropertyOf)\s+rdf:resource="[^"]*#([A-Za-z0-9_]+)"', b):
            edges.append((child, pm.group(1)))
    return edges


def main() -> int:
    ap = argparse.ArgumentParser(description="Cross-peer filler inventory for SCORE core slots")
    ap.add_argument("--measurement", action="store_true", help="restrict to measurement/operator slots")
    args = ap.parse_args()

    core = FORMAL / "score-core.owl"
    core_names = set(re.findall(r'rdf:about="[^"]*#([A-Za-z0-9_]+)"', core.read_text(encoding="utf-8")))

    # parent(core) -> { impl -> [children] }
    fillers: dict[str, dict[str, list[str]]] = {}
    for p in sorted(FORMAL.glob("score-*.owl")):
        if p.name == "score-core.owl":
            continue
        impl = impl_of(p)
        for child, parent in parse(p):
            if parent in core_names:
                fillers.setdefault(parent, {}).setdefault(impl, []).append(child)

    slots = sorted(MEASUREMENT_SLOTS if args.measurement else core_names)
    shared, local, unfilled = [], [], []
    for slot in slots:
        f = fillers.get(slot, {})
        (shared if len(f) >= 2 else local if len(f) == 1 else unfilled).append(slot)

    def show(label: str, names: list[str]) -> None:
        print(f"\n=== {label} ({len(names)}) ===")
        for slot in names:
            f = fillers.get(slot, {})
            if f:
                parts = "; ".join(f"{impl}:{','.join(cs)}" for impl, cs in sorted(f.items()))
                print(f"  core:{slot}\n      {parts}")
            else:
                print(f"  core:{slot}")

    show("SHARED  (>=2 peers -- consensus-eligible; audit semantic agreement)", shared)
    show("LOCAL   (1 peer -- domain-specific or latent-shared)", local)
    show("UNFILLED (0 peers)", unfilled)

    print(f"\nsummary: {len(shared)} shared | {len(local)} local | {len(unfilled)} unfilled"
          + f"  (over {'measurement slots' if args.measurement else 'all core constructs'})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
