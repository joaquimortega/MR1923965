#!/usr/bin/env python3
"""Check that no declaration statement changed between a reference commit and a target tree.

Usage: python3 scripts/check_statements.py [REF] [TARGET_DIR]
  REF         git ref of the reviewed scaffold (default: scaffold-reviewed)
  TARGET_DIR  working tree to compare (default: repository root)

For every `theorem`/`lemma`/`def`/`abbrev`/`structure`/`instance` in `FourierFrames/**`
present at REF (in the same file, or, if moved, anywhere in `FourierFrames/**`), the statement (text from the keyword to the first top-level `:=`, `where` or
`|`, whitespace-normalised, comments removed) must be identical in TARGET_DIR.  New declarations
are allowed; removed or changed ones are reported.  Exit code 1 if anything changed.
"""
import pathlib, re, subprocess, sys

root = pathlib.Path(__file__).resolve().parent.parent
ref = sys.argv[1] if len(sys.argv) > 1 else "scaffold-reviewed"
target = pathlib.Path(sys.argv[2]).resolve() if len(sys.argv) > 2 else root

KW = r"(?:private\s+|protected\s+|noncomputable\s+|@\[[^\]]*\]\s*)*(theorem|lemma|def|abbrev|structure|instance|class)\s+"
decl_re = re.compile(r"^" + KW + r"([^\s:(\[{]+)", re.M)


def strip_comments(s: str) -> str:
    s = re.sub(r"/-.*?-/", " ", s, flags=re.S)  # block and doc comments (non-nested is enough here)
    return re.sub(r"--[^\n]*", " ", s)


def statements(text: str) -> dict:
    text = strip_comments(text)
    out = {}
    ms = list(decl_re.finditer(text))
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(text)
        chunk = text[m.start():end]
        # cut at the first top-level ':=' / ' where' / leading '|' (pattern-matching defs)
        cut = len(chunk)
        for pat in (":=", "\nwhere", " where\n", "\n  |"):
            j = chunk.find(pat)
            if j != -1:
                cut = min(cut, j)
        key = m.group(2)
        out[key] = " ".join(chunk[:cut].split())
    return out


def files_at_ref():
    ls = subprocess.run(["git", "-C", str(root), "ls-tree", "-r", "--name-only", ref,
                         "FourierFrames"], capture_output=True, text=True, check=True)
    for path in ls.stdout.split():
        if path.endswith(".lean"):
            txt = subprocess.run(["git", "-C", str(root), "show", f"{ref}:{path}"],
                                 capture_output=True, text=True, check=True).stdout
            yield path, txt


# Coordinator-approved removals/changes of non-main helper statements found false during
# implementation: name -> reason (each recorded in NOTEBOOK.md).
APPROVED = {
    "compB_eq_zero_iff": "unused hypothesis removed, NOTEBOOK I-03",
    "compB_mul_Q": "unused hypothesis removed, NOTEBOOK I-03",
    "tendsto_polyB": "unused hypothesis removed, NOTEBOOK I-03",
    "phase_rigidity": "unused hypothesis removed, NOTEBOOK I-03",
    "multU_const_mul": "unused hypothesis removed, NOTEBOOK I-03",
    "memPW_of_memHE": "unused hypothesis removed, NOTEBOOK I-03",
    "HEEqPW.phaseDeriv_mul_sq_ge": "unused hypothesis removed, NOTEBOOK I-03",
    "osc_bound_of_JN": "unused hypothesis removed, NOTEBOOK I-03",
    "integrable_log_mul_sub_one": "unused hypothesis removed, NOTEBOOK I-03",
    "isSampling_of_replace_finite": "unused hypothesis removed, NOTEBOOK I-03",
    "sampInner_self": "unused hypothesis removed, NOTEBOOK I-03",
    "sampInner_conj_symm": "unused hypothesis removed, NOTEBOOK I-03",
    "sampInner_smul_left": "unused hypothesis removed, NOTEBOOK I-03",
    "samp_H3": "unused hypothesis removed, NOTEBOOK I-03",
    "summable_norm_herglotz": "unused hypothesis removed, NOTEBOOK I-03",
    "entSum_eq": "unused hypothesis removed, NOTEBOOK I-03",
    "herglotzEnt_eq": "unused hypothesis removed, NOTEBOOK I-03",
    "exists_noRealZero_hb": "unused hypothesis removed, NOTEBOOK I-03",
    "HEEqPW.levelSet_ineq": "unused hypothesis removed, NOTEBOOK I-03",
    "HEEqPW.levelSet_cis": "unused hypothesis removed, NOTEBOOK I-03",
    "RegData.hasSum_UPsi": "unused hypothesis removed, NOTEBOOK I-03",
    "RegData.abs_cellTerm_below": "unused hypothesis removed, NOTEBOOK I-03",
    "RegData.abs_cellTerm_above": "unused hypothesis removed, NOTEBOOK I-03",
    "theorem2_i": "unused hypothesis removed, NOTEBOOK I-03",
    "theorem2_ii": "unused hypothesis removed, NOTEBOOK I-03",
    "sampCore": "def -> abbrev (class-valued def must be reducible; set_option removed), NOTEBOOK I-03",
}


def all_statements(base: pathlib.Path) -> dict:
    """All candidates for moved declarations, including equal short names in other namespaces."""
    out = {}
    for p in sorted((base / "FourierFrames").rglob("*.lean")):
        for name, st in statements(p.read_text()).items():
            out.setdefault(name, []).append(st)
    return out


bad = 0
for path, old in files_at_ref():
    new_path = target / path
    if not new_path.exists():
        print(f"REMOVED FILE {path}")
        bad += 1
        continue
    olds, local = statements(old), statements(new_path.read_text())
    # Prefer the original file. For moved declarations inspect every candidate:
    # e.g. FF.Pavlov.cell must not shadow the frozen FF.cell merely
    # because its new file sorts first.
    elsewhere = all_statements(target) if any(n not in local for n in olds) else {}
    for name, st in olds.items():
        candidates = [local[name]] if name in local else elsewhere.get(name, [])
        if name in APPROVED:
            if st not in candidates:
                print(f"approved change {path}: {name} ({APPROVED[name]})")
            continue
        if not candidates:
            print(f"REMOVED {path}: {name}")
            bad += 1
        elif st not in candidates:
            print(f"CHANGED {path}: {name}\n  old: {st}\n  new: {candidates[0]}")
            bad += 1
print("OK: no statement changed" if bad == 0 else f"{bad} problem(s)")
sys.exit(1 if bad else 0)
