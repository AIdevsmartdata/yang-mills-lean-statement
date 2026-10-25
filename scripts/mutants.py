#!/usr/bin/env python3
"""Mutation tests for the v1.1 theorems of ClayYM (q-form of the gap, closure lemma, vacuum, guards).

Each mutant changes ONE piece of text in a copy of the sources (never the sources themselves),
then compiles the mutated copy with `lake env lean` against the already-built library.
A mutant passes the test ("killed") only if
  * the unmutated control file of the same group compiles (RC = 0, no `error`), and
  * the mutated file FAILS (RC != 0), with at least one `error` inside the declaration named as its
    target. This is a LOCALISED failure of the existing proof (possibly through a cascade from an
    earlier error, which is reported): it certifies a dependency of the derivation, not by itself a
    mathematical obstruction. Semantic necessity is established only by the guard theorems
    (SpectralLadder, HiddenVacuum, HiddenSlowMode).
Files are written under logs/mutants/. Exit code 0 only if every mutant is killed.

Groups (single files; a mutation of Transfer.lean is tested together with the file that uses it):
  T   = Transfer.lean
  TL  = Transfer.lean + Fake/SpectralLadder.lean
  TH  = Transfer.lean + Fake/HiddenVacuum.lean
  TG  = Transfer.lean + GapQ.lean
  THS = Transfer.lean + Fake/HiddenVacuum.lean + Fake/HiddenSlowMode.lean
"""
import os
import re
import subprocess
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
OUT = os.path.join(ROOT, "logs", "mutants")
LEAN_CMD = os.environ.get("CLAYYM_LEAN_CMD", "lake env lean").split()
TIMEOUT = int(os.environ.get("CLAYYM_MUTANT_TIMEOUT", "1200"))


def read(rel):
    with open(os.path.join(ROOT, rel), encoding="utf-8") as f:
        return f.read()


def body(src):
    """Source without its `import` lines (kept in the header of the combined file)."""
    return "\n".join(l for l in src.splitlines() if not l.startswith("import "))


def imports(src):
    return [l for l in src.splitlines() if l.startswith("import ")]


FILES = {
    "T": "ClayYM/Transfer.lean",
    "L": "ClayYM/Fake/SpectralLadder.lean",
    "H": "ClayYM/Fake/HiddenVacuum.lean",
    "S": "ClayYM/Fake/HiddenSlowMode.lean",
    "G": "ClayYM/GapQ.lean",
}
MODULES = {k: "import " + v[:-5].replace("/", ".") for k, v in FILES.items()}


def combine(group, srcs):
    """Concatenate the files of a group into one compilable file (imports of the inlined modules dropped)."""
    keys = list(group)
    inlined = {MODULES[k] for k in keys}
    imps = []
    for k in keys:
        for l in imports(srcs[k]):
            if l not in inlined and l not in imps:
                imps.append(l)
    parts = ["\n".join(imps)]
    for k in keys:
        parts.append("-- ===== " + FILES[k] + " =====\n" + body(srcs[k]))
    return "\n".join(parts) + "\n"


# (name, group, file key, anchor or None, old text, new text, target declaration, theorem guarded)
MUTANTS = [
    ("M01_ladder_constant_energy", "TL", "L", None,
     "def lam (n : ℕ) : ℝ := (n : ℝ)⁻¹",
     "def lam (n : ℕ) : ℝ := if n = 0 then 0 else 1",
     "theorem not_qGap", "Ladder.not_qGap / truncation_inference_fails"),
    ("M02_trunc_uniform_q", "TL", "L", None,
     "QGapOn ops ladder (D N) ℓ (Real.exp (-(ℓ * (N : ℝ)⁻¹)))",
     "QGapOn ops ladder (D N) ℓ (Real.exp (-ℓ))",
     "theorem trunc_qGap", "Ladder.trunc_qGap"),
    ("M03_qgap_q_le_one", "TL", "T", None,
     "  0 < ℓ ∧ 0 < q ∧ q < 1 ∧\n    ∀ A ∈ 𝒜₀, B (o.trunc B A) (o.trunc B A) ℓ ≤ q * B (o.trunc B A) (o.trunc B A) 0",
     "  0 < ℓ ∧ 0 < q ∧ q ≤ 1 ∧\n    ∀ A ∈ 𝒜₀, B (o.trunc B A) (o.trunc B A) ℓ ≤ q * B (o.trunc B A) (o.trunc B A) 0",
     "theorem not_qGap", "QGapOn (q < 1) via Ladder.not_qGap"),
    ("M04_qgap_strict_ineq", "T", "T", None,
     "  0 < ℓ ∧ 0 < q ∧ q < 1 ∧\n    ∀ A ∈ 𝒜₀, B (o.trunc B A) (o.trunc B A) ℓ ≤ q * B (o.trunc B A) (o.trunc B A) 0",
     "  0 < ℓ ∧ 0 < q ∧ q < 1 ∧\n    ∀ A ∈ 𝒜₀, B (o.trunc B A) (o.trunc B A) ℓ < q * B (o.trunc B A) (o.trunc B A) 0",
     "theorem QGapOn.of_tendsto", "Transfer.QGapOn.of_tendsto (closure needs a non-strict inequality)"),
    ("M05_gap_to_q_wrong_q", "T", "T", None,
     "(hℓ : 0 < ℓ) (𝒜₀ : Set V) : QGapOn o B 𝒜₀ ℓ (Real.exp (-(Δ * ℓ)))",
     "(hℓ : 0 < ℓ) (𝒜₀ : Set V) : QGapOn o B 𝒜₀ ℓ (Real.exp (-(2 * Δ * ℓ)))",
     "theorem MassGapOn.qGapOn", "Transfer.MassGapOn.qGapOn"),
    ("M06_decay_rate_doubled", "T", "T", None,
     "∀ t, 0 ≤ t → ∀ w, ⟪ω, w⟫ = 0 → ‖T t w‖ ≤ q ^ (t / ℓ) * ‖w‖ := by",
     "∀ t, 0 ≤ t → ∀ w, ⟪ω, w⟫ = 0 → ‖T t w‖ ≤ q ^ (2 * t / ℓ) * ‖w‖ := by",
     "theorem decay_of_qbound", "Transfer.decay_of_qbound"),
    ("M07_recon_without_symmetry", "T", "T", None,
     "  T_symm : ∀ t, 0 ≤ t → ∀ x y, ⟪T t x, y⟫ = ⟪x, T t y⟫\n",
     "",
     "theorem massGapOn_of_qGapOn", "Recon.massGapOn_of_qGapOn (self-adjointness used)"),
    ("M08_recon_without_contraction", "T", "T", None,
     "  T_contr : ∀ t, 0 ≤ t → ‖T t‖ ≤ 1\n",
     "",
     "theorem massGapOn_of_qGapOn", "Recon.massGapOn_of_qGapOn (contraction used)"),
    ("M09_drop_density", "T", "T", "theorem massGapOn_of_qGapOn",
     "    (hd : ∀ w : r.H, ⟪r.ω, w⟫ = 0 → w ∈ closure (r.cls '' (o.trunc B '' 𝒜₀))) :",
     "    (hd : True) :",
     "theorem massGapOn_of_qGapOn", "Recon.massGapOn_of_qGapOn (density used)"),
    ("M10_vacuum_zero", "T", "T", "theorem vacuum_unique",
     "(w : r.H) (hw : r.T ℓ w = w) : w = ⟪r.ω, w⟫ • r.ω := by",
     "(w : r.H) (hw : r.T ℓ w = w) : w = 0 := by",
     "theorem vacuum_unique", "Recon.vacuum_unique"),
    ("M11_opnorm_without_projection", "T", "T", "theorem massGapOn_univ_iff_opNorm",
     "      0 < Δ ∧ ∀ t, 0 ≤ t → ‖(r.T t).comp r.perp‖ ≤ Real.exp (-(Δ * t)) := by",
     "      0 < Δ ∧ ∀ t, 0 ≤ t → ‖r.T t‖ ≤ Real.exp (-(Δ * t)) := by",
     "theorem massGapOn_univ_iff_opNorm", "Recon.massGapOn_univ_iff_opNorm (P_Ω needed)"),
    ("M12_hidden_algebra_cyclic", "TH", "H", None,
     "def A0 : Set E3 := {v | v 2 = 0}",
     "def A0 : Set E3 := Set.univ",
     "lemma trunc_visible", "HiddenVacuum.qGap / density_needed"),
    ("M13_massgap_bridge", "TG", "T", None,
     "    |B F G t - B F o.Ω 0 * B o.Ω G 0| ≤\n      Real.exp (-(Δ * t)) * Real.sqrt (B F F 0) * Real.sqrt (B G G 0)",
     "    |B F G t - B F o.Ω 0 * B o.Ω G 0| ≤\n      Real.exp (-(Δ * t / 2)) * Real.sqrt (B F F 0) * Real.sqrt (B G G 0)",
     "theorem hasMassGap_iff_massGapOn", "hasMassGap_iff_massGapOn (bridge to HasMassGap)"),
    ("M14_qgap_bridge", "TG", "G", None,
     "    rpForm R S (truncFam R S A) (truncFam R S A) ℓ ≤\n      q * rpForm R S (truncFam R S A) (truncFam R S A) 0",
     "    rpForm R S (truncFam R S A) (truncFam R S A) ℓ <\n      q * rpForm R S (truncFam R S A) (truncFam R S A) 0",
     "theorem qGap_iff_qGapOn", "qGap_iff_qGapOn (bridge to QGapOn)"),
    ("M15_closure_own_q", "TG", "G", "theorem QGap.of_tendsto",
     "(hconv : SchwingerConvergesOn L R Sk S 𝒜₀ ℓ) (h : ∀ᶠ k in L, QGap R (Sk k) 𝒜₀ ℓ q) :",
     "(hconv : SchwingerConvergesOn L R Sk S 𝒜₀ ℓ) (h : ∀ᶠ k in L, ∃ q', QGap R (Sk k) 𝒜₀ ℓ q') :",
     "theorem QGap.of_tendsto", "QGap.of_tendsto (same q; see Ladder.closure_needs_same_q)"),
    ("M16_trivRecon_zero_transfer", "TG", "G", None,
     "  T := fun _ => ContinuousLinearMap.id ℝ ℝ",
     "  T := fun _ => 0",
     "def trivRecon", "trivRecon (non-vacuity of the named hypothesis)"),
    ("M17_hasMassGap_qGap_wrong_q", "TG", "G", None,
     "    QGap R S 𝒜₀ ℓ (Real.exp (-(Δ * ℓ))) :=",
     "    QGap R S 𝒜₀ ℓ (Real.exp (-(2 * Δ * ℓ))) :=",
     "theorem HasMassGap.qGap", "HasMassGap.qGap"),
    ("M18_qgap_to_gap_wrong_rate", "TG", "G", "theorem QGap.hasMassGap",
     "(hd : TruncDense rec 𝒜₀) : HasMassGap R S (-Real.log q / ℓ) :=",
     "(hd : TruncDense rec 𝒜₀) : HasMassGap R S (-2 * Real.log q / ℓ) :=",
     "theorem QGap.hasMassGap", "QGap.hasMassGap"),
    ("M19_ladder_massgap_uniform", "TL", "L", None,
     "theorem trunc_massGap (N : ℕ) (hN : 1 ≤ N) : MassGapOn ops ladder (D N) (1 / N) := by",
     "theorem trunc_massGap (N : ℕ) (hN : 1 ≤ N) : MassGapOn ops ladder (D N) 1 := by",
     "theorem trunc_massGap", "Ladder.trunc_massGap"),
    ("M20_ladder_no_gap_on_truncation", "TL", "L", None,
     "theorem not_massGap (Δ : ℝ) : ¬ MassGapOn ops ladder Set.univ Δ := by",
     "theorem not_massGap (Δ : ℝ) : ¬ MassGapOn ops ladder (D 1) Δ := by",
     "theorem not_massGap", "Ladder.not_massGap"),
    ("M21_ladder_inference_on_D0", "TL", "L", None,
     "      Monotone D → (∀ N, ∃ q, QGapOn o B (D N) ℓ q) → ∃ q, QGapOn o B (⋃ N, D N) ℓ q := by",
     "      Monotone D → (∀ N, ∃ q, QGapOn o B (D N) ℓ q) → ∃ q, QGapOn o B (D 0) ℓ q := by",
     "theorem truncation_inference_fails", "Ladder.truncation_inference_fails"),
    ("M22_approx_gapless_above_N", "TL", "L", None,
     "def lamN (N n : ℕ) : ℝ := if n ≤ N then lam n else 1",
     "def lamN (N n : ℕ) : ℝ := if n ≤ N then lam n else 0",
     "theorem approx_qGap", "Ladder.approx_qGap / closure_needs_same_q"),
    ("M23_hidden_gap_on_visible", "TH", "H", None,
     "theorem not_massGap (Δ : ℝ) : ¬ MassGapOn ops B Set.univ Δ := by",
     "theorem not_massGap (Δ : ℝ) : ¬ MassGapOn ops B A0 Δ := by",
     "theorem not_massGap", "HiddenVacuum.not_massGap"),
    ("M24_hidden_second_vacuum_e1", "TH", "H", None,
     "    recon.T ℓ (e 2) = e 2 ∧ e 2 ≠ ⟪recon.ω, e 2⟫ • recon.ω := by",
     "    recon.T ℓ (e 1) = e 1 ∧ e 2 ≠ ⟪recon.ω, e 2⟫ • recon.ω := by",
     "theorem second_vacuum", "HiddenVacuum.second_vacuum / uniqueness_needs_density"),
    ("M25_limit_normalisation", "TG", "G", "theorem normalized_of_tendsto",
     "(hn : ∀ᶠ k in L, Sk k [] = 1) : S [] = 1 := by",
     "(hn : ∀ᶠ k in L, Sk k [] = 1) : S [] = 0 := by",
     "theorem normalized_of_tendsto", "normalized_of_tendsto"),
    ("M26_equivalence_on_empty_set", "TG", "G", "theorem exists_hasMassGap_iff_exists_qGap",
     "    (∃ Δ, HasMassGap R S Δ) ↔ ∃ q, QGap R S Set.univ ℓ q :=",
     "    (∃ Δ, HasMassGap R S Δ) ↔ ∃ q, QGap R S ∅ ℓ q :=",
     "theorem exists_hasMassGap_iff_exists_qGap", "exists_hasMassGap_iff_exists_qGap"),
    ("M27_limit_without_normalisation", "TG", "G", "theorem hasMassGap_of_tendsto",
     "    (hn : ∀ᶠ k in L, Sk k [] = 1) (rec : OSReconstruction R S) (hd : TruncDense rec 𝒜₀) :\n    HasMassGap R S (-Real.log q / ℓ) :=",
     "    (hn : True) (rec : OSReconstruction R S) (hd : TruncDense rec 𝒜₀) :\n    HasMassGap R S (-Real.log q / ℓ) :=",
     "theorem hasMassGap_of_tendsto", "hasMassGap_of_tendsto"),
    ("M28_clay_vacuum_zero", "TG", "G", "theorem QGap.vacuum_unique",
     "(hd : TruncDense rec 𝒜₀) (w : rec.H) (hw : rec.T ℓ w = w) : w = ⟪rec.ω, w⟫ • rec.ω :=",
     "(hd : TruncDense rec 𝒜₀) (w : rec.H) (hw : rec.T ℓ w = w) : w = 0 :=",
     "theorem QGap.vacuum_unique", "QGap.vacuum_unique"),
    ("M29_truncDense_empty", "TG", "G", "theorem truncDense_univ",
     "    TruncDense rec Set.univ :=",
     "    TruncDense rec ∅ :=",
     "theorem truncDense_univ", "truncDense_univ"),
    ("M30_vac_vac_value", "TG", "G", None,
     "    rpForm R S (vac ι) (vac ι) t = S [] := by",
     "    rpForm R S (vac ι) (vac ι) t = 2 * S [] := by",
     "lemma rpForm_vac_vac", "rpForm_vac_vac"),
    ("M31_slow_mode_gap_quarter", "THS", "S", None,
     "theorem not_massGap_one : ¬ MassGapOn ops B2 Set.univ 1 := by",
     "theorem not_massGap_one : ¬ MassGapOn ops B2 Set.univ (1 / 4) := by",
     "theorem not_massGap_one", "HiddenSlowMode.not_massGap_one / density_needed_unique_vacuum"),
    ("M32_slow_mode_vacuum_zero", "THS", "S", None,
     "    w = ⟪recon2.ω, w⟫ • recon2.ω := by",
     "    w = 0 := by",
     "theorem vacuum_unique2", "HiddenSlowMode.vacuum_unique2"),
]

# Declared type of each mutant: D = a definition is changed; H = a hypothesis is removed or weakened
# (measures a dependency of the derivation, not the semantic necessity of the hypothesis); C = a conclusion
# is strengthened (the mutated statement is false or at least not proved by the same argument); M = a guard
# model or construction is changed.
TYPES = {'M01': 'M', 'M02': 'C', 'M03': 'D', 'M04': 'D', 'M05': 'C', 'M06': 'C', 'M07': 'H', 'M08': 'H', 'M09': 'H', 'M10': 'C', 'M11': 'C', 'M12': 'M', 'M13': 'D', 'M14': 'D', 'M15': 'H', 'M16': 'M', 'M17': 'C', 'M18': 'C', 'M19': 'C', 'M20': 'C', 'M21': 'C', 'M22': 'M', 'M23': 'C', 'M24': 'C', 'M25': 'C', 'M26': 'C', 'M27': 'H', 'M28': 'C', 'M29': 'C', 'M30': 'C', 'M31': 'C', 'M32': 'C'}


def apply_mutation(src, anchor, old, new):
    start = 0
    if anchor is not None:
        start = src.find(anchor)
        if start < 0:
            raise ValueError("anchor not found: " + anchor)
    i = src.find(old, start)
    if i < 0:
        raise ValueError("text to mutate not found: " + old[:60])
    if anchor is None and src.count(old) != 1:
        raise ValueError("text to mutate is not unique: " + old[:60])
    return src[:i] + new + src[i + len(old):]


DECL = re.compile(r"^\s*(@\[[^\]]*\]\s*)*((private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"
                  r"(theorem|lemma|def|abbrev|structure|class|inductive|instance|example|attribute|end\b|namespace|section|/-)")


def decl_range(text, target):
    """Line range [a, b) of the declaration starting with `target` (up to the next declaration)."""
    lines = text.splitlines()
    pat = re.compile(r"^\s*(@\[[^\]]*\]\s*)*((private|protected|noncomputable)\s+)*" + re.escape(target) + r"(\s|$)")
    starts = [i for i, l in enumerate(lines) if pat.match(l)]
    if not starts:
        raise ValueError("target declaration not found: " + target)
    if len(starts) > 1:
        raise ValueError("target declaration not unique: " + target)
    a = starts[0]
    decl = DECL
    b = len(lines)
    for j in range(a + 1, len(lines)):
        if decl.match(lines[j]):
            b = j
            break
    return a + 1, b + 1  # 1-based, half-open


def compile_file(path, log):
    with open(log, "w", encoding="utf-8") as f:
        try:
            rc = subprocess.run(LEAN_CMD + [path], cwd=ROOT, stdout=f, stderr=subprocess.STDOUT,
                                timeout=TIMEOUT).returncode
        except subprocess.TimeoutExpired:
            rc = 124
    with open(log, encoding="utf-8") as f:
        out = f.read()
    return rc, out


def error_lines(out, path):
    base = os.path.basename(path)
    res = []
    for m in re.finditer(re.escape(base) + r":(\d+):\d+: error", out):
        res.append(int(m.group(1)))
    return res


def main():
    os.makedirs(OUT, exist_ok=True)
    srcs = {k: read(v) for k, v in FILES.items()}
    controls = {}
    ok = True
    for g in sorted({m[1] for m in MUTANTS}):
        p = os.path.join(OUT, "control_" + g + ".lean")
        with open(p, "w", encoding="utf-8") as f:
            f.write(combine(g, srcs))
        rc, out = compile_file(p, p[:-5] + ".log")
        n_err = len(error_lines(out, p))
        controls[g] = (rc == 0 and n_err == 0)
        print(f"control {g:3s}: RC={rc} errors={n_err} -> {'OK' if controls[g] else 'FAIL'}")
        ok &= controls[g]
    killed = 0
    for (name, g, k, anchor, old, new, target, guarded) in MUTANTS:
        msrcs = dict(srcs)
        try:
            msrcs[k] = apply_mutation(srcs[k], anchor, old, new)
        except ValueError as e:
            print(f"{name}: SETUP ERROR ({e})")
            ok = False
            continue
        text = combine(g, msrcs)
        p = os.path.join(OUT, name + ".lean")
        with open(p, "w", encoding="utf-8") as f:
            f.write(text)
        rc, out = compile_file(p, p[:-5] + ".log")
        errs = error_lines(out, p)
        try:
            a, b = decl_range(text, target)
        except ValueError as e:
            print(f"{name}: SETUP ERROR ({e})")
            ok = False
            continue
        in_target = [l for l in errs if a <= l < b]
        before = [l for l in errs if l < a]
        is_killed = controls[g] and rc != 0 and len(in_target) > 0
        killed += is_killed
        ok &= is_killed
        print(f"{name} [{TYPES[name[:3]]}]: RC={rc} errors={len(errs)} in target '{target}'={len(in_target)} "
              f"(earlier errors: {len(before)}) -> {'KILLED' if is_killed else 'SURVIVED'}   [guards {guarded}]")
    print(f"MUTANTS: {killed}/{len(MUTANTS)} killed")
    print("MUTATION TESTS: PASS" if ok else "MUTATION TESTS: FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
