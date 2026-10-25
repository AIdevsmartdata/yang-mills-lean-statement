/-
ClayYM/Inhabited/SU2Exp.lean
============================
The Lie algebra `𝔤_ρ = {X | ∀ t ∈ ℝ, exp(tX) ∈ ρ(SU(2))}` (definition of `Group.lean`, with
Mathlib's matrix exponential `NormedSpace.exp`) is exactly `su(2)`.

Tool: a 2×2 Jacobi formula, `d/du det(exp(uY)) = tr(Y) · det(exp(uY))`, which gives both
`tr Y = 0 ⟹ det exp(uY) = 1` and `det exp(uX) ≡ 1 ⟹ tr X = 0`. Anti-Hermiticity comes from the
uniqueness of the derivative at `0` of `u ↦ exp(u Xᴴ) = exp(−u X)`.

This file also tests that the matrix exponential is not the "junk" value `1` of Mathlib's
definition: otherwise `𝔤_ρ` would be the whole of `M₂(ℂ)`, not simple, and the class of groups
would be empty.
-/
import ClayYM.Inhabited.SU2Topology

open Matrix Topology

noncomputable section

namespace ClayYM

namespace SU2

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Projection onto the entry `(i, j)`, as a continuous `ℝ`-linear map. -/
def entryCLM (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

lemma entryCLM_apply (i j : Fin 2) (M : Matrix (Fin 2) (Fin 2) ℂ) : entryCLM i j M = M i j := rfl

/-- `u ↦ exp(u • Y)` has derivative `Y * exp(u • Y)`. -/
lemma hasDerivAt_expY (Y : Matrix (Fin 2) (Fin 2) ℂ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => NormedSpace.exp (v • Y)) (Y * NormedSpace.exp (u • Y)) u :=
  hasDerivAt_exp_smul_const' Y u

lemma hasDerivAt_entry (Y : Matrix (Fin 2) (Fin 2) ℂ) (u : ℝ) (i j : Fin 2) :
    HasDerivAt (fun v : ℝ => NormedSpace.exp (v • Y) i j)
      ((Y * NormedSpace.exp (u • Y)) i j) u := by
  have h := (entryCLM i j).hasFDerivAt.comp_hasDerivAt u (hasDerivAt_expY Y u)
  exact h

/-- 2×2 Jacobi formula: `d/du det(exp(uY)) = tr(Y) det(exp(uY))`. -/
lemma hasDerivAt_det_exp (Y : Matrix (Fin 2) (Fin 2) ℂ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => (NormedSpace.exp (v • Y)).det)
      (Y.trace * (NormedSpace.exp (u • Y)).det) u := by
  set F := fun v : ℝ => NormedSpace.exp (v • Y)
  have h00 := hasDerivAt_entry Y u 0 0
  have h01 := hasDerivAt_entry Y u 0 1
  have h10 := hasDerivAt_entry Y u 1 0
  have h11 := hasDerivAt_entry Y u 1 1
  have hdet : (fun v : ℝ => (NormedSpace.exp (v • Y)).det) =
      fun v => F v 0 0 * F v 1 1 - F v 0 1 * F v 1 0 := by
    funext v; rw [Matrix.det_fin_two]
  rw [hdet]
  have hd := (h00.mul h11).sub (h01.mul h10)
  convert hd using 1
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- If `tr Y = 0`, then `det exp(uY) = 1` for every `u`. -/
lemma det_exp_of_trace_zero {Y : Matrix (Fin 2) (Fin 2) ℂ} (hY : Y.trace = 0) (u : ℝ) :
    (NormedSpace.exp (u • Y)).det = 1 := by
  have hdiff : Differentiable ℝ (fun v : ℝ => (NormedSpace.exp (v • Y)).det) :=
    fun v => (hasDerivAt_det_exp Y v).differentiableAt
  have hderiv : ∀ v, deriv (fun v : ℝ => (NormedSpace.exp (v • Y)).det) v = 0 := by
    intro v
    rw [(hasDerivAt_det_exp Y v).deriv, hY, zero_mul]
  have := is_const_of_deriv_eq_zero hdiff hderiv u 0
  rw [this]
  simp

/-- `exp(u Y)` is unitary if `Yᴴ = −Y`. -/
lemma exp_mul_star_of_antiherm {Y : Matrix (Fin 2) (Fin 2) ℂ} (hY : Y.conjTranspose = -Y) (u : ℝ) :
    NormedSpace.exp (u • Y) * star (NormedSpace.exp (u • Y)) = 1 := by
  have hstar : star (NormedSpace.exp (u • Y)) = NormedSpace.exp (-(u • Y)) := by
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, conjTranspose_smul, hY]
    simp
  rw [hstar, Matrix.exp_neg]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp (u • Y)))

/-- The image of `ρ` (as a set of matrices) is `SU(2)`. -/
lemma range_ρ : Set.range (fun g : G => ((ρ g : Matrix.unitaryGroup (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ)) = (Matrix.specialUnitaryGroup (Fin 2) ℂ : Set _) := by
  ext A
  constructor
  · rintro ⟨g, rfl⟩
    exact g.2
  · intro hA
    exact ⟨⟨A, hA⟩, rfl⟩

lemma coe_smul_eq (t : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) : (t : ℂ) • X = t • X := by
  ext i j
  simp [Complex.real_smul]

/-- `su(2) ⊆ 𝔤_ρ`. -/
lemma su2_subset : su2 ⊆ lieAlgebraOf ρ := by
  intro Y hY t
  rw [range_ρ, coe_smul_eq]
  rw [SetLike.mem_coe, mem_su_iff]
  exact ⟨exp_mul_star_of_antiherm hY.1 t, det_exp_of_trace_zero hY.2 t⟩

/-- `𝔤_ρ ⊆ su(2)`. -/
lemma subset_su2 : lieAlgebraOf ρ ⊆ su2 := by
  intro X hX
  have hmem : ∀ u : ℝ, NormedSpace.exp (u • X) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    intro u
    have := hX u
    rwa [range_ρ, coe_smul_eq] at this
  refine ⟨?_, ?_⟩
  · -- anti-Hermiticity: uniqueness of the derivative at 0
    have heq : (fun u : ℝ => NormedSpace.exp (u • X.conjTranspose)) =
        fun u : ℝ => NormedSpace.exp (u • (-X)) := by
      funext u
      have hU := ((mem_su_iff _).mp (hmem u)).1
      have hinv : (NormedSpace.exp (u • X))⁻¹ = star (NormedSpace.exp (u • X)) :=
        Matrix.inv_eq_right_inv hU
      rw [smul_neg, Matrix.exp_neg, hinv, Matrix.star_eq_conjTranspose,
        ← Matrix.exp_conjTranspose, conjTranspose_smul]
      simp
    have h1 := hasDerivAt_expY X.conjTranspose 0
    have h2 := hasDerivAt_expY (-X) 0
    rw [heq] at h1
    have := h1.unique h2
    simpa using this
  · -- zero trace: derivative of det exp(uX) ≡ 1
    have hconst : (fun u : ℝ => (NormedSpace.exp (u • X)).det) = fun _ => (1 : ℂ) := by
      funext u
      exact ((mem_su_iff _).mp (hmem u)).2
    have h1 := hasDerivAt_det_exp X 0
    rw [hconst] at h1
    have h2 : HasDerivAt (fun _ : ℝ => (1 : ℂ)) 0 0 := hasDerivAt_const 0 1
    have := h1.unique h2
    simpa using this

/-- `𝔤_ρ = su(2)`. -/
theorem lieAlgebra_eq : lieAlgebraOf ρ = su2 := Set.Subset.antisymm subset_su2 su2_subset

/-- The Lie algebra of SU(2) (defined through the exponential) is simple. -/
theorem simple : IsSimpleLieAlg (lieAlgebraOf ρ) := by
  rw [lieAlgebra_eq]
  exact isSimpleLieAlg_su2

end SU2

end ClayYM
