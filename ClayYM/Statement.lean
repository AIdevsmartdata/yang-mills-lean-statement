/-
ClayYM/Statement.lean
=====================
Candidate statements of the Clay problem "Yang–Mills Existence and Mass Gap" (Jaffe–Witten §4):

  "Prove that for any compact simple gauge group G, a non-trivial quantum Yang–Mills theory exists
    on ℝ⁴ and has a mass gap Δ > 0. Existence includes establishing axiomatic properties at least as
    strong as those cited in [45, 35]."

These are DEFINITIONS (`def … : Prop`). No `theorem … := sorry`: the open statement is nowhere
declared proved.

* `ClayYM_A`  (lattice limit): the Euclidean theory is a limit (a → 0, volume → ∞,
  β → ∞) of the Wilson measures of the group `G` itself; "this is Yang–Mills for G" is therefore
  CONSTRUCTED (the action and the Haar measure are those of `G`); the limit satisfies OS (with the
  OS 1975 linear growth), is non-trivial (21 non-zero components, `m < ∞`), has a mass gap
  `Δ`, and this same `Δ` holds in EVERY extension by scalar gauge-invariant local observables
  (C-odd sectors included) that has an OS limit.
* `ClayYM_B`  (axiomatic): an OS theory on ℝ⁴ whose fields are the components of
  `Tr F_{μν}F_{ρσ}` (tensor representation of O(4)), with a mass gap, `m < ∞`, and the
  Yang–Mills fingerprint (conserved stress tensor normalised by Ward; asymptotic freedom:
  `⟨θθ⟩ ~ κ/log²` with `κ = 3 dim G/π⁴` imposed, universal correction `−b₁/b₀²`,
  `C_T = dim G × C_T(Maxwell)`; indecomposability). Faithful only up to `dim G` among simple
  groups (see STATEMENT.md).
* `ClayYM_AB`: the conjunction (lattice limit AND fingerprint), the strongest one: the recommended
  reference statement.
-/
import ClayYM.Lattice

open MeasureTheory Filter Topology

noncomputable section

namespace ClayYM

/-- Component-wise non-triviality: each of the components `Tr F_{μν}F_{ρσ}`
(`μ ≠ ν`, `ρ ≠ σ`) has a connected two-point function that is not identically zero. -/
def ComponentsNontrivial (S : Schwinger YMIdx 4) : Prop :=
  ∀ α : YMIdx, α.1 ≠ α.2.1 → α.2.2.1 ≠ α.2.2.2 →
    ∃ x : Spacetime 4, x ≠ 0 ∧ conn2 S (Pi.single α 1) (Pi.single α 1) x 0 ≠ 0

section LatticeClauses

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] {N : ℕ}

/-- The gap `Δ` also holds in every extension of the limit by gauge-invariant local observables
(treated as even scalar fields), as soon as their smeared correlations (joint with the plaquette
components) converge to an OS theory. -/
def GapInAllLocalExtensions (ρ : G →* Matrix.unitaryGroup (Fin N) ℂ) (sq : LatticeSeq)
    (Z : ℕ → Matrix YMIdx YMIdx ℝ) (c : ℕ → YMIdx → ℝ) (Δ : ℝ) : Prop :=
  ∀ (r m : ℕ) (O : Fin m → LocalObs G r), (∀ q, GaugeInvariantLocal (O q)) →
    ∀ (Z' : ℕ → Matrix (Fin m) (Fin m) ℝ) (c' : ℕ → Fin m → ℝ)
      (S' : Schwinger (YMIdx ⊕ Fin m) 4),
      LatticeConverges ρ sq
          (fun k U y => jointField ρ O (sq.L k) (sq.a k) (Z k) (c k) (Z' k) (c' k) U y) S' →
        OSAxioms (jointRep m) S' → HasMassGap (jointRep m) S' Δ

/-- The clauses of variant A for a given representation `ρ` (the one of the Wilson action), limit
`S`, sequence of lattices and renormalisations. -/
structure LatticeYMClauses (ρ : G →* Matrix.unitaryGroup (Fin N) ℂ) (S : Schwinger YMIdx 4)
    (sq : LatticeSeq) (Z : ℕ → Matrix YMIdx YMIdx ℝ) (c : ℕ → YMIdx → ℝ) (Δ : ℝ) : Prop where
  os : OSAxioms tensorRep4 S
  tensor_symmetric : TensorSymmetric S
  components_nontrivial : ComponentsNontrivial S
  converges : LatticeConverges ρ sq (fun k U y α => renField ρ (sq.a k) (Z k) (c k) U y α) S
  mass_gap : HasMassGap tensorRep4 S Δ
  finite_mass : FiniteMass tensorRep4 S
  gap_all_sectors : GapInAllLocalExtensions ρ sq Z c Δ

end LatticeClauses

/-- **Variant A (Wilson lattice limit).** For every compact simple group `G`, there exist a
continuous faithful unitary representation `ρ'` (choice of the Wilson action: the regularisation
is not imposed by Clay) and a continuum limit satisfying all the clauses. -/
def ClayYM_A : Prop :=
  ∀ K : CompactSimpleGroup, ∃ (N' : ℕ) (ρ' : K.G →* Matrix.unitaryGroup (Fin N') ℂ),
    Continuous ρ' ∧ Function.Injective ρ' ∧
    ∃ (S : Schwinger YMIdx 4) (sq : LatticeSeq) (Z : ℕ → Matrix YMIdx YMIdx ℝ)
      (c : ℕ → YMIdx → ℝ) (Δ : ℝ), LatticeYMClauses ρ' S sq Z c Δ

/-- **Variant B (axiomatic + Yang–Mills fingerprint).** -/
def ClayYM_B : Prop :=
  ∀ K : CompactSimpleGroup, ∃ S : Schwinger YMIdx 4,
    OSAxioms tensorRep4 S ∧ ClayMassGap tensorRep4 S ∧ ComponentsNontrivial S ∧ YMFingerprint K S

/-- **Variant AB (lattice limit AND fingerprint).** -/
def ClayYM_AB : Prop :=
  ∀ K : CompactSimpleGroup, ∃ (N' : ℕ) (ρ' : K.G →* Matrix.unitaryGroup (Fin N') ℂ),
    Continuous ρ' ∧ Function.Injective ρ' ∧
    ∃ (S : Schwinger YMIdx 4) (sq : LatticeSeq) (Z : ℕ → Matrix YMIdx YMIdx ℝ)
      (c : ℕ → YMIdx → ℝ) (Δ : ℝ), LatticeYMClauses ρ' S sq Z c Δ ∧ YMFingerprint K S

/-- Check: AB implies A. -/
theorem ClayYM_AB.toA (h : ClayYM_AB) : ClayYM_A := by
  intro K
  obtain ⟨N', ρ', hc, hi, S, sq, Z, c, Δ, hA, _⟩ := h K
  exact ⟨N', ρ', hc, hi, S, sq, Z, c, Δ, hA⟩

/-- Check: AB implies B. -/
theorem ClayYM_AB.toB (h : ClayYM_AB) : ClayYM_B := by
  intro K
  obtain ⟨N', ρ', -, -, S, sq, Z, c, Δ, hA, hF⟩ := h K
  exact ⟨S, hA.os, ⟨⟨Δ, hA.mass_gap⟩, hA.finite_mass⟩, hA.components_nontrivial, hF⟩

end ClayYM
