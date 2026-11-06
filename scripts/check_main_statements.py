#!/usr/bin/env python3
"""Check that every main theorem of `comparator/statements.lean` appears in `FourierFrames/**`
with the identical statement (whitespace-normalised; comments ignored).

For each `theorem NAME ... := by` in comparator/statements.lean the text from `theorem` to the
first `:=` must occur verbatim, modulo whitespace, in some file under FourierFrames/ (in namespace
`FF`).  Exit code 1 if a theorem is missing or its statement differs.
Run from the repository root:  python3 scripts/check_main_statements.py
"""
import pathlib, re, sys

root = pathlib.Path(__file__).resolve().parent.parent


def strip_comments(s: str) -> str:
    s = re.sub(r"/-.*?-/", " ", s, flags=re.S)
    return re.sub(r"--[^\n]*", " ", s)


def norm(s: str) -> str:
    return " ".join(s.split())


stmts = strip_comments((root / "comparator" / "statements.lean").read_text())
main = {}
for m in re.finditer(r"^theorem\s+(\S+)(.*?):=", stmts, flags=re.M | re.S):
    main[m.group(1)] = norm("theorem " + m.group(1) + m.group(2))

project = {}
for p in sorted((root / "FourierFrames").rglob("*.lean")):
    if p.name == "Defs.lean":
        continue
    text = strip_comments(p.read_text())
    for m in re.finditer(r"^theorem\s+(\S+)(.*?):=", text, flags=re.M | re.S):
        project.setdefault(m.group(1), []).append((p, norm("theorem " + m.group(1) + m.group(2))))

bad = 0
for name, st in main.items():
    found = project.get(name, [])
    if not found:
        print(f"MISSING {name}")
        bad += 1
    elif not any(s == st for _, s in found):
        print(f"DIFFERENT {name}\n  expected: {st}\n  found:    {found[0][1]}  ({found[0][0].relative_to(root)})")
        bad += 1
    elif len(found) > 1:
        print(f"DUPLICATE {name}: {[str(p.relative_to(root)) for p, _ in found]}")
        bad += 1
print(f"OK: all {len(main)} main statements present verbatim" if bad == 0 else f"{bad} problem(s)")
sys.exit(1 if bad else 0)
