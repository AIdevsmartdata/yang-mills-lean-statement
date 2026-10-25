# ClayYM: a candidate Lean 4 statement of the Yang–Mills existence and mass gap problem, with compiled guards against fake models

> **Status: candidate statement, unreviewed.** This repository contains Lean 4 *definitions* (`def … : Prop`) and compiled sanity checks. It is **not** a proof, a partial proof, or any progress on the Yang–Mills existence and mass gap problem, and nothing here asserts that the statements are true. The Lean code and the texts were written by AI agents under the direction of the author (see [AI use](#ai-use)). Please read [Limitations](#limitations) before using these statements.

This project is not affiliated with, reviewed by, or endorsed by the Clay Mathematics Institute. "Clay" in the name refers only to the problem statement it attempts to formalise.

## What this is

Lean 4 / Mathlib definitions of three candidate formal statements of the Clay Millennium problem "Yang–Mills existence and mass gap" (A. Jaffe and E. Witten, official problem description), together with compiled *guard* and control theorems. Forty-four of them are listed and audited in `ClayYM/Audit.lean`; the library contains 248 theorems in total, and every declaration depends only on the three standard axioms `propext`, `Classical.choice` and `Quot.sound`.

The guards show that known fake models (the trivial theory, free fields, U(1), decoupled products, …) do not satisfy the statements, and that the quantifier "for every compact simple gauge group" is not vacuous (SU(2) is an instance).

The purpose is to propose precise formal *targets* and to expose them to criticism. They are candidate formalisations: the recommended one (`ClayYM_AB`) is a candidate *sufficient* criterion, not an equivalent reformulation of the Clay problem (see [Limitations](#limitations)). `STATEMENT.md` gives the clause-by-clause correspondence with the Clay text, the design choices, the fake models and the comparison with other public formalisations.

## What this is not

- Not a proof, a partial proof, or a result about Yang–Mills theory. The three statements are open; no `theorem … := sorry` declares them proved.
- Not an official, endorsed or community-reviewed formalisation of the Clay problem.
- Not reviewed by an independent human expert (see [AI use](#ai-use)).

## The statements (`ClayYM/Statement.lean`)

| Name | Content (informal) |
|---|---|
| `ClayYM.ClayYM_A` | For every compact simple group `G`, there are a faithful unitary representation and a sequence of 4D Wilson lattice measures for `G` (`a → 0`, physical volume `→ ∞`, `β → ∞`). Their renormalised plaquette fields `Tr F_{μν}F_{ρσ}` converge to Euclidean Schwinger kernels that satisfy the Osterwalder–Schrader axioms, are non-trivial (21 non-zero components, `m < ∞`), and have a mass gap `Δ > 0`. The same `Δ` holds in every extension by local gauge-invariant observables that has an OS limit. |
| `ClayYM.ClayYM_B` | For every compact simple `G`, there are OS Schwinger kernels for the 21 components of `Tr F_{μν}F_{ρσ}` with a mass gap, `m < ∞`, and a "Yang–Mills fingerprint". The fingerprint consists of: a conserved stress tensor normalised by the energy Ward identity; the short-distance trace-anomaly two-point function `⟨θθ⟩ ~ κ/(x⁸ log² x)` with `κ = 3 dim G/π⁴` (FP1) and the universal next-to-leading correction `−b₁/b₀² = −102/121` (FP2); `C_T = dim G × C_T(Maxwell)` (FP3); and indecomposability (no decoupled sectors). |
| `ClayYM.ClayYM_AB` | `A ∧ fingerprint`, the recommended reference statement. Proved: `ClayYM_AB.toA` and `ClayYM_AB.toB`. |

The framework is Euclidean: Schwinger kernels at non-coincident points, and OS axioms with a pointwise growth bound that suffices for the OS 1975 linear-growth condition. The mass gap is written as exponential decay of truncated correlations of the OS reflection form. Through OS reconstruction, which is **not formalised here**, this is equivalent to `spec H ⊂ {0} ∪ [Δ, ∞)` with a unique vacuum. The clause `m < ∞` is Jaffe–Witten's.

## Limitations

These limitations are declared, not hidden; read them before using the statements.

1. **The Wilson route (method).** Variants A and AB require the theory to be the continuum limit of Wilson's lattice action, with a renormalisation of fixed form (`Φ = Z·Q − c`). The Clay problem fixes no route: a construction by any other method satisfies A only if one also proves convergence of the Wilson lattice approximation to it. A and AB are therefore candidate *sufficient* formal criteria, not equivalent reformulations of the Clay problem.
2. **OS reconstruction is not formalised.** The link to the Wightman axioms and to the spectrum of the Hamiltonian is the classical Osterwalder–Schrader theorem, used on paper only. The pointwise growth bound is a sufficient form of OS 1975 condition E0′; we argue, but do not prove, that true Yang–Mills satisfies it. If it did not, the statements would be false for true Yang–Mills.
3. **Partial field content.** Only the 21 components of `Tr F_{μν}F_{ρσ}` (dimension 4) are fields of the theory. Higher local operators enter only through `GapInAllLocalExtensions` (variant A), which is an implication and is empty if no extension converges. In B, the gap covers only the sector generated by these 21 components (C-even). There is no operator product expansion.
4. **"This is Yang–Mills for G" is a modelling choice.** In A it rests on the universality of lattice limits, which is a physical belief, not a theorem. B identifies G only up to `dim G` among simple groups: for example, Spin(7) and Sp(6) are not distinguished. This is why AB is recommended.
5. **The fingerprint constants are perturbative predictions**: `κ = 3 dim G/π⁴`, `−102/121` and `C_T = 4 dim G/π⁴`. If one of them were wrong, B and AB would be false for true Yang–Mills. They are checked by a SymPy script and were re-derived in separate runs by AI agents; these re-derivations are not independent human checks (see [AI use](#ai-use)).
6. **Other coverage gaps.** At θ = π, a topological phase is not excluded by B. Proca fields, charged matter and massless Gaussian limits are rejected by argument only.
7. **The stress-tensor normalisation is pinned by argument, not by a Lean lemma.** In `YMFingerprint`, `z₁` and `z₂` are existential. `Conserved` fixes `z₂/z₁` unless the `F²` correlators are position-independent, and in that case FP1 fails. `WardEnergy` fixes the overall scale. So `κ` is not a tunable parameter, but this argument is not formalised.
8. **The guards are clause-level.** Most of them read "any theory whose two-point function is X violates clause Y". Only the trivial theory is constructed as a full OS theory.

## Defects found in public formal statements of the same problem

- **lean-dojo/LeanMillenniumPrizeProblems.** Its README already acknowledges the defect: the Yang–Mills statement is "Statement incomplete, not a valid target", and "the existence statement can therefore be satisfied by a two-dimensional toy model" ([README, section "Known incomplete statements", commit `603053dc`](https://github.com/lean-dojo/LeanMillenniumPrizeProblems/blob/603053dc267cf3efe422f438eb78098c0ececd6f/README.md#known-incomplete-statements)). For this work we compiled such a toy model against their exact definitions; it is not included here (`STATEMENT.md`, §1.1).
- **lixiang90/math-challenge-millennium** (the copy used by math-challenge.org, workspace `generated/millennium_yang_mills`, commit `34dab7c7`). Its `vacuum_unique` axiom is contradictory, so the prize target `clay_prize_yang_mills` is equivalent to "no compact simple gauge group exists". This was reported, with a compiled witness, in [issue #2](https://github.com/lixiang90/math-challenge-millennium/issues/2) on 2026-10-25 (`STATEMENT.md`, §1.2).

## Correspondence with the Clay text (Jaffe–Witten, §3–§4)

| Clay text | Lean | Status |
|---|---|---|
| "for any compact simple gauge group G" | `CompactSimpleGroup`: compact connected group with a faithful continuous unitary representation whose exp-defined Lie algebra is simple | Non-vacuous: SU(2) is an instance (`compactSimpleGroup_nonempty`, `SU2.lieAlgebra_eq`, `SU2.dim_eq_three`). Connectedness is imposed, which is the usual reading; non-connected groups with simple Lie algebra (e.g. O(3)) are excluded |
| "exists on ℝ⁴", "axiomatic properties at least as strong as [Streater–Wightman, Osterwalder–Schrader]" | `OSAxioms` (E0, E0′ as a pointwise bound, E1 under ℝ⁴ ⋊ O(4), E2, E3, E4) | The passage to the Wightman axioms uses OS reconstruction (not formalised) |
| "H has no spectrum in (0, Δ)", "m < ∞" | `HasMassGap`, `FiniteMass` | The equivalence with the spectral form uses OS reconstruction |
| "local quantum field operators in correspondence with the gauge-invariant local polynomials in F and its covariant derivatives, such as Tr F_ij F_kl" | the 21 components of `Tr F_{μν}F_{ρσ}` (rank-4 tensor representation of O(4)); higher operators only through `GapInAllLocalExtensions` (A) | Partial |
| "agree at short distances with the predictions of asymptotic freedom … existence of a stress tensor and an operator product expansion" | `Conserved`, `WardEnergy`, `UVTrace`, `UVStress` (B, AB) | No OPE |
| §6.5 Wilson lattice approximation; footnote 2 (weak existence excluded unless the limit has the gap and the axioms) | `wilsonAction`, `LatticeSeq`, `LatticeConverges`; A requires OS, gap and `m < ∞` of the limit | A subsequence is allowed |

## Guards (compiled, `ClayYM/Fake/`, `ClayYM/Inhabited/`)

- **Trivial theory.** It satisfies all OS axioms and has every `Δ` as a gap. It is rejected by `FiniteMass`, and in B also by FP1. The trivial limit of genuine Wilson measures (`Z = 0`) satisfies every A clause except `finite_mass` and `components_nontrivial` (`trivial_wilson_limit`).
- **Free scalar field of any mass, as any Wick polynomial without derivatives.** Rejected by FP1 (`gff_wick_not_UVTrace`). The heat-kernel bounds are proved; the Wick identity itself is a hypothesis of the guard and is not formalised.
- **Free gluons, and any exactly conformal theory.** They pass FP3 but fail FP1 (`freeGluons_mutation`, `not_UVTrace_of_zero`).
- **U(1) and every group whose faithful representation has dimension ≤ 1.** Excluded by simplicity (`not_simple_dim_one`).
- **Decoupled sums of two non-trivial OS theories,** for example `YM_{G₁} ⊗ YM_{G₂}` with `dim G₁ + dim G₂ = dim G`. They pass FP1–FP3, because the UV data are additive (`uvFingerprint_indepSum`). They are rejected only by indecomposability (`indepSum_not_YMFingerprint`).
- **Local sector of 2D Yang–Mills.** Rejected by `FiniteMass` (`ym2d_local_sector_not_finiteMass`). The fact that this local sector is trivial is cited, not formalised.

The full list, with the statements of the guards, is printed by `ClayYM/Audit.lean` (44 `#print axioms` lines).

## How to verify

Requirements: [elan](https://github.com/leanprover/elan), git, network access for the Mathlib build cache (about 8 GB on disk for the dependencies), and, for the constants check, `python3` with SymPy (which brings mpmath). The versions are pinned in `lean-toolchain` (Lean `v4.34.0`) and `lake-manifest.json` (Mathlib `v4.34.0`, rev `5ed2965256430c3649e86755f9576b54eca72435`). There are no other dependencies.

```bash
git clone https://github.com/AIdevsmartdata/yang-mills-lean-statement.git
cd yang-mills-lean-statement
scripts/verify.sh
```

The script runs `lake exe cache get`, `lake build ClayYM` and `lake build ClayYM.Audit`. It then runs `scripts/AuditAll.lean`, which collects the axioms of **every** declaration in the `ClayYM` namespace, not only the 44 listed in `Audit.lean`. Finally it runs `constants/sympy_constantes.py`, which prints its results to standard output and writes no file, saves that output in `logs/constantes_obtenues.txt`, and compares it with the committed reference `constants/constantes_verifiees.txt` using `diff`. It exits with code 0 only if all of the following hold:
- every build returns 0;
- no log line contains `error`;
- there is no `sorry` and no `sorryAx`;
- every declaration depends only on `propext`, `Classical.choice`, `Quot.sound`;
- there are no `axiom` declarations;
- `ClayYM_A`, `ClayYM_B` and `ClayYM_AB` are definitions;
- the SymPy script returns 0 and its output is identical to `constants/constantes_verifiees.txt`.

Expected summary (observed on a fresh copy of this repository, 2026-10-25):

```
AUDIT ClayYM: 430 constants, 248 theorems, 0 axiom declarations, 0 constants with non-standard axioms
STATEMENT ClayYM.ClayYM_A: definition (Prop), OK
STATEMENT ClayYM.ClayYM_B: definition (Prop), OK
STATEMENT ClayYM.ClayYM_AB: definition (Prop), OK
sympy_constantes.py  RC=0
constants: output identical to constants/constantes_verifiees.txt
VERIFY: PASS
```

Negative controls: adding `theorem t : (1 : ℕ) = 2 := by sorry` to the namespace makes the script print `NON-STANDARD: … depends on [sorryAx]` and `VERIFY: FAIL`. Changing a value in `constants/constantes_verifiees.txt` makes it print `constants: output DIFFERS …` and `VERIFY: FAIL`.

The labels printed by the SymPy script (and the file names under `constants/`) are in French; they were kept unchanged when the comments were translated into English, so that the committed reference output stays byte-identical to the one checked before the translation.

An additional check with an independent kernel was run locally on 2026-10-25 and is not part of the script: nanoda 0.4.19, on a `lean4export` dump of the 44 guards and the 3 statements, reported "Checked 51133 declarations with no errors", with only the three standard axioms.

## Repository layout

| Path | Contents |
|---|---|
| `ClayYM/Basic.lean` | ℝ^d, O(d), time reflection θ, configurations, test functions °S₊, families |
| `ClayYM/OS.lean` | Schwinger kernels, reflection form, `OSAxioms` (E0, E0′, E1–E4) |
| `ClayYM/Gap.lean` | `HasMassGap`, `FiniteMass` (m < ∞), `ClayMassGap` |
| `ClayYM/Group.lean` | `CompactSimpleGroup` (faithful ρ, Lie algebra through exp, simplicity), `dim`, `b₀`, `b₁` |
| `ClayYM/Fingerprint.lean` | `YMIdx`, `tensorRep4`, `TensorSymmetric`, `T(z₁,z₂)`, `Conserved`, `WardEnergy`, `UVTrace` (FP1, FP2), `traceAnomalyCoeff` (κ), `UVStress` (FP3), `Decomposable`, `YMFingerprint` |
| `ClayYM/Lattice.lean` | torus, Haar measure, Wilson action, plaquettes, `LatticeSeq`, `LatticeConverges`, local observables |
| `ClayYM/Statement.lean` | **`ClayYM_A`, `ClayYM_B`, `ClayYM_AB`** (`def … : Prop`) |
| `ClayYM/Fake/*.lean` | fake models and guards |
| `ClayYM/Inhabited/*.lean` | SU(2) is a `CompactSimpleGroup`, `dim SU(2) = 3` |
| `ClayYM/Audit.lean` | `#print axioms` of the 44 guards and controls (not part of the default target) |
| `scripts/verify.sh`, `scripts/AuditAll.lean` | build, axiom audit of every declaration, constants check |
| `constants/` | SymPy script for the fingerprint constants and its expected output |
| `STATEMENT.md` | correspondence with the Clay text, design choices, risks, fake models, comparisons |
| `CITATION.cff`, `.zenodo.json` | citation metadata |

## Related work

- `lean-dojo/LeanMillenniumPrizeProblems` (Apache-2.0) marks its own Yang–Mills statement as "statement incomplete, not a valid target".
- `prove2me/formalpedia` (Apache-2.0) has a Yang–Mills proxy that is labelled as needing review. Its Wilson-limit and Lie-algebra definitions are close to ours; the two were written independently.

No code from these or other repositories is copied here. ClayYM depends only on Mathlib.

## References

- A. Jaffe, E. Witten, *Quantum Yang–Mills Theory*, official problem description of the Clay Mathematics Institute, https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf.
- K. Osterwalder, R. Schrader, Commun. Math. Phys. 31 (1973) 83–112, doi:10.1007/BF01645738, and 42 (1975) 281–305, doi:10.1007/BF01608978.
- K. Osterwalder, E. Seiler, Ann. Phys. 110 (1978) 440–471, doi:10.1016/0003-4916(78)90039-8.
- H. Osborn, A. Petkou, Ann. Phys. 231 (1994) 311–362, doi:10.1006/aphy.1994.1045.
- J. C. Collins, A. Duncan, S. D. Joglekar, Phys. Rev. D 16 (1977) 438–449, doi:10.1103/PhysRevD.16.438.
- W. E. Caswell, Phys. Rev. Lett. 33 (1974) 244–246, doi:10.1103/PhysRevLett.33.244; D. R. T. Jones, Nucl. Phys. B 75 (1974) 531–538, doi:10.1016/0550-3213(74)90093-5.
- Mathlib and the Lean FRO (Apache-2.0).

## AI use

Author: Kévin Rémondière, sole human author, independent researcher. No other person is an author of this work.

**Declaration.** The Lean code and the texts of this repository (this README, `STATEMENT.md`, the code comments and the scripts) were written by AI agents (Claude, Anthropic) under the direction of Kévin Rémondière. The verifications are mechanical: Lean kernel builds, an automatic axiom audit of every declaration, a SymPy script compared with a committed reference output, and, run locally, an independent kernel (nanoda). No expert human review has been carried out to date.

**Human review of the constants FP1–FP3:** the repository owner approved this release on 25 October 2026. No independent expert review of these constants has been carried out; checks by specialists are welcome (please open an issue).

| Task | Tool | How it was checked |
|---|---|---|
| Lean definitions, guard proofs, scripts, README, `STATEMENT.md`, English translation of the comments | Claude (Anthropic), under the author's direction | Lean kernel (`lake build`), `scripts/AuditAll.lean`, independent kernel nanoda (local); the translation of the comments left every declaration unchanged (identical structural hashes, before and after, of all 526 constants of the `ClayYM` namespace, internal ones included) |
| Adversarial review of fidelity (found and fixed a reduction of the first version of B to SU(2)) | Claude reviewer instances | Each fix is backed by a compiled guard (`indepSum_not_YMFingerprint`, `uvFingerprint_indepSum`) |
| Physical constants of the fingerprint | Claude + SymPy | `constants/sympy_constantes.py` (its output is compared with `constants/constantes_verifiees.txt` by `scripts/verify.sh`), and re-derivations of `κ`, `c_{F²} = 48/π⁴`, `−102/121` and `C_T` in separate AI agent runs (not independent human checks) |

What was **not** done: an independent human review of the statement, of the physical constants, or of the faithfulness to the Clay text. The adversarial reviews mentioned in this repository were performed by AI models, which are not independent referees. Please treat this as an unreviewed proposal.

## Citation

See `CITATION.cff`. A Zenodo DOI will be added after the first release.

## License

Apache License 2.0 (see `LICENSE` and `NOTICE`), the same licence as Mathlib. Copyright 2026 Kévin Rémondière.
