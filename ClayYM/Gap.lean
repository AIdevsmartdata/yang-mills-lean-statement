/-
ClayYM/Gap.lean
===============
Mass gap in Euclidean form, and finite mass.

Jaffe–Witten §4: "A quantum field theory has a mass gap Δ if H has no spectrum in the interval
(0, Δ) for some Δ > 0. The supremum of such Δ is the mass m, and we require m < ∞."

Euclidean form used (equivalent through the Osterwalder–Schrader reconstruction, where
`⟪F, τ_t G⟫ = ⟨F, e^{-tH} G⟩` and `Ω` is the class of the family `vac`):
  `|⟪F, τ_t G⟫ − ⟪F, Ω⟫⟪Ω, G⟫| ≤ e^{−Δ t} ‖F‖ ‖G‖`  for every `t ≥ 0` and all families `F, G`,
which is equivalent to `‖e^{−tH}(1 − P_Ω)‖ ≤ e^{−Δt}`, i.e. `spec(H) ⊂ {0} ∪ [Δ, ∞)` AND `ker H = ℂΩ`
(unique vacuum). This equivalence relies on the OS reconstruction theorem (not formalised here).
-/
import ClayYM.OS

open MeasureTheory Filter Topology

noncomputable section

namespace ClayYM

variable {ι : Type} {d : ℕ}

/-- `Δ` is a mass gap: exponential decay at rate `Δ` of all truncated correlations
(reflection form), uniformly over the families of test functions. -/
def HasMassGap [Fintype ι] [NeZero d] (R : CompRep ι d) (S : Schwinger ι d) (Δ : ℝ) : Prop :=
  0 < Δ ∧ ∀ (F G : Family ι d) (t : ℝ), 0 ≤ t →
    |rpForm R S F G t - rpForm R S F (vac ι) 0 * rpForm R S (vac ι) G 0| ≤
      Real.exp (-(Δ * t)) * Real.sqrt (rpForm R S F F 0) * Real.sqrt (rpForm R S G G 0)

/-- The mass `m = sup {Δ | Δ mass gap}` (equal to `0` by Mathlib's convention if the set is not
bounded above or is empty; used for documentation only). -/
def mass [Fintype ι] [NeZero d] (R : CompRep ι d) (S : Schwinger ι d) : ℝ :=
  sSup {Δ : ℝ | HasMassGap R S Δ}

/-- "we require m < ∞": the set of mass gaps is bounded above. -/
def FiniteMass [Fintype ι] [NeZero d] (R : CompRep ι d) (S : Schwinger ι d) : Prop :=
  BddAbove {Δ : ℝ | HasMassGap R S Δ}

/-- Mass gap in the Clay sense: some `Δ > 0` exists, and the mass is finite. -/
def ClayMassGap [Fintype ι] [NeZero d] (R : CompRep ι d) (S : Schwinger ι d) : Prop :=
  (∃ Δ, HasMassGap R S Δ) ∧ FiniteMass R S

/-- Consistency check: a smaller gap is still a gap (the set of gaps is an interval
`]0, m]` or `]0, m[`). -/
theorem HasMassGap.mono [Fintype ι] [NeZero d] {R : CompRep ι d} {S : Schwinger ι d}
    {Δ Δ' : ℝ} (h : HasMassGap R S Δ) (h0 : 0 < Δ') (hle : Δ' ≤ Δ) : HasMassGap R S Δ' := by
  refine ⟨h0, fun F G t ht => (h.2 F G t ht).trans ?_⟩
  have hexp : Real.exp (-(Δ * t)) ≤ Real.exp (-(Δ' * t)) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right hle ht
    linarith
  have hs : 0 ≤ Real.sqrt (rpForm R S F F 0) * Real.sqrt (rpForm R S G G 0) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc Real.exp (-(Δ * t)) * Real.sqrt (rpForm R S F F 0) * Real.sqrt (rpForm R S G G 0)
      = Real.exp (-(Δ * t)) * (Real.sqrt (rpForm R S F F 0) * Real.sqrt (rpForm R S G G 0)) := by
        ring
    _ ≤ Real.exp (-(Δ' * t)) * (Real.sqrt (rpForm R S F F 0) * Real.sqrt (rpForm R S G G 0)) :=
        mul_le_mul_of_nonneg_right hexp hs
    _ = Real.exp (-(Δ' * t)) * Real.sqrt (rpForm R S F F 0) * Real.sqrt (rpForm R S G G 0) := by
        ring

end ClayYM
