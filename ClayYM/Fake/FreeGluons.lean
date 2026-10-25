/-
ClayYM/Fake/FreeGluons.lean
===========================
FAKE MODEL: "free gluons" = `dim G` free Maxwell fields (Yang–Mills at zero coupling).
Their stress tensor is traceless and its two-point function is EXACTLY
`C_T ℐ_{μν,ρσ}(x̂)/|x|⁸` with `C_T = dim G · 4/π⁴` (checked by `constants/sympy_constantes.py`).

Mutation test of FP1 (proved): every theory whose function `⟨T T⟩_c` is exactly that one
SATISFIES FP3 (`UVStress`) but VIOLATES FP1 (`UVTrace`). Without FP1, the fingerprint would let the
free theory through; FP1 (the logarithmic trace anomaly) is the clause that encodes the interaction.
More generally, FP1 excludes every scale-invariant theory (θ ≡ 0), in particular every CFT.
-/
import ClayYM.Fake.Lemmas

open MeasureTheory Filter Topology

noncomputable section

namespace ClayYM

/-- `⟨T_{μν}(x) T_{ρσ}(0)⟩_c = C · ℐ_{μν,ρσ}(x/|x|) / |x|⁸` exactly (conformal form). -/
def ExactConformalStress (S : Schwinger YMIdx 4) (z₁ z₂ C : ℝ) : Prop :=
  ∀ x : Spacetime 4, x ≠ 0 → ∀ μ ν ρ σ : Fin 4,
    conn2 S (Tc z₁ z₂ μ ν) (Tc z₁ z₂ ρ σ) x 0 = C * confI (‖x‖⁻¹ • x) μ ν ρ σ / ‖x‖ ^ 8

/-- An exactly conformal `⟨TT⟩` forces `⟨θθ⟩_c ≡ 0`, hence violates FP1. -/
theorem exactConformal_not_UVTrace (S : Schwinger YMIdx 4) (z₁ z₂ C κ : ℝ) (hκ : κ ≠ 0)
    (h : ExactConformalStress S z₁ z₂ C) : ¬ UVTrace S z₁ z₂ κ := by
  apply not_UVTrace_of_zero S z₁ z₂ κ hκ
  intro x hx
  have hu : ‖‖x‖⁻¹ • x‖ = 1 := norm_smul_inv_norm hx
  rw [conn2_θc]
  simp_rw [h x hx]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun ρ _ => ?_)
  rw [← Finset.sum_div, ← Finset.mul_sum, confI_traceless hu, mul_zero, zero_div]

/-- The same function, with `C = dim G · 4/π⁴`, satisfies FP3. -/
theorem exactConformal_UVStress (K : CompactSimpleGroup) (S : Schwinger YMIdx 4) (z₁ z₂ : ℝ)
    (h : ExactConformalStress S z₁ z₂ ((K.dim : ℝ) * (4 / Real.pi ^ 4))) :
    UVStress K S z₁ z₂ := by
  intro u hu μ ν ρ σ
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : (0 : ℝ) < s := hs
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu
    exact zero_ne_one hu
  have hsu : s • u ≠ 0 := smul_ne_zero hs'.ne' hu0
  have hn : ‖s • u‖ = s := by rw [norm_smul, hu, mul_one, Real.norm_of_nonneg hs'.le]
  have hdir : ‖s • u‖⁻¹ • (s • u) = u := by
    rw [hn, smul_smul, inv_mul_cancel₀ hs'.ne', one_smul]
  rw [h (s • u) hsu, hdir, hn]
  field_simp

/-- **Mutation test of FP1.** The "free gluons" structure passes FP3 and fails FP1. -/
theorem freeGluons_mutation (K : CompactSimpleGroup) (S : Schwinger YMIdx 4) (z₁ z₂ : ℝ)
    (h : ExactConformalStress S z₁ z₂ ((K.dim : ℝ) * (4 / Real.pi ^ 4))) :
    UVStress K S z₁ z₂ ∧ ¬ UVTrace S z₁ z₂ (traceAnomalyCoeff K) :=
  ⟨exactConformal_UVStress K S z₁ z₂ h,
    exactConformal_not_UVTrace S z₁ z₂ _ _ (traceAnomalyCoeff_pos K).ne' h⟩

/-- Consequence: no "free gluons" theory satisfies the fingerprint with this `T`. -/
theorem freeGluons_not_fingerprint_with (K : CompactSimpleGroup) (S : Schwinger YMIdx 4)
    (h : ∀ z₁ z₂ : ℝ, ∃ C, ExactConformalStress S z₁ z₂ C) : ¬ YMFingerprint K S := by
  rintro ⟨-, ⟨z₁, z₂, -, -, -, hT, -⟩, -⟩
  obtain ⟨C, hC⟩ := h z₁ z₂
  exact exactConformal_not_UVTrace S z₁ z₂ C _ (traceAnomalyCoeff_pos K).ne' hC hT

end ClayYM
