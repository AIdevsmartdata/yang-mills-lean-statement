/-
ClayYM/Inhabited/SU2Algebra.lean
================================
Algebra of `su(2) = {X ∈ M₂(ℂ) | Xᴴ = −X, tr X = 0}`: basis `e₁, e₂, e₃`, brackets
`[e₁,e₂] = 2e₃`, `[e₂,e₃] = 2e₁`, `[e₃,e₁] = 2e₂`, decomposition of the elements, and SIMPLICITY in
the sense of `IsSimpleLieAlg` (non-abelian; every real subspace stable under `[su(2), ·]` is `0` or
`su(2)`). Purely algebraic (no analysis).
-/
import ClayYM.Group

open Matrix

noncomputable section

namespace ClayYM

namespace SU2

/-- `su(2)` as a subset of `M₂(ℂ)`. -/
def su2 : Set (Matrix (Fin 2) (Fin 2) ℂ) := {X | X.conjTranspose = -X ∧ X.trace = 0}

/-- `e₁ = diag(i, −i)`. -/
def e1 : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I]
/-- `e₂ = [[0, 1], [−1, 0]]`. -/
def e2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]
/-- `e₃ = [[0, i], [i, 0]]`. -/
def e3 : Matrix (Fin 2) (Fin 2) ℂ := !![0, Complex.I; Complex.I, 0]

/-- Commutator. -/
def br (X Y : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ := X * Y - Y * X

lemma e1_mem : e1 ∈ su2 := by
  refine ⟨?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [e1, conjTranspose_apply]
  · simp [e1, Matrix.trace_fin_two]

lemma e2_mem : e2 ∈ su2 := by
  refine ⟨?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [e2, conjTranspose_apply]
  · simp [e2, Matrix.trace_fin_two]

lemma e3_mem : e3 ∈ su2 := by
  refine ⟨?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [e3, conjTranspose_apply]
  · simp [e3, Matrix.trace_fin_two]

lemma br_e1_e2 : br e1 e2 = (2 : ℝ) • e3 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [br, e1, e2, e3, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma br_e2_e3 : br e2 e3 = (2 : ℝ) • e1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [br, e1, e2, e3, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma br_e3_e1 : br e3 e1 = (2 : ℝ) • e2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [br, e1, e2, e3, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma br_e2_e1 : br e2 e1 = -((2 : ℝ) • e3) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [br, e1, e2, e3, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma br_e3_e2 : br e3 e2 = -((2 : ℝ) • e1) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [br, e1, e2, e3, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma br_e1_e3 : br e1 e3 = -((2 : ℝ) • e2) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [br, e1, e2, e3, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Real coordinates of an element of `su(2)`. -/
def c1 (X : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := (X 0 0).im
def c2 (X : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := (X 0 1).re
def c3 (X : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := (X 0 1).im

/-- Combination `x₁e₁ + x₂e₂ + x₃e₃` (real coefficients). -/
def comb (x1 x2 x3 : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := x1 • e1 + x2 • e2 + x3 • e3

/-- Every element of `su(2)` is `c₁ e₁ + c₂ e₂ + c₃ e₃`. -/
lemma eq_comb {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X ∈ su2) : X = comb (c1 X) (c2 X) (c3 X) := by
  obtain ⟨hH, hT⟩ := hX
  have h00 := congrFun (congrFun hH 0) 0
  have h01 := congrFun (congrFun hH 1) 0
  simp only [conjTranspose_apply, RCLike.star_def] at h00 h01
  rw [Matrix.trace_fin_two] at hT
  have r00 : (X 0 0).re = 0 := by
    have := congrArg Complex.re h00
    simp only [Complex.conj_re, Matrix.neg_apply, Complex.neg_re] at this
    linarith
  have h10 : X 1 0 = -(starRingEnd ℂ) (X 0 1) := by
    rw [h01, Matrix.neg_apply, neg_neg]
  have h11 : X 1 1 = -X 0 0 := by linear_combination hT
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [comb, c1, c2, c3, e1, e2, e3, h10, h11, Complex.ext_iff, r00]

lemma comb_mem (x1 x2 x3 : ℝ) : comb x1 x2 x3 ∈ su2 := by
  refine ⟨?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [comb, e1, e2, e3, conjTranspose_apply] <;> ring_nf
  · simp [comb, e1, e2, e3, Matrix.trace_fin_two]

/-- Double brackets: `Y + ¼ [e_k, [e_k, Y]] = y_k e_k` for `Y = y₁e₁ + y₂e₂ + y₃e₃`. -/
lemma proj1 (x1 x2 x3 : ℝ) :
    comb x1 x2 x3 + (1 / 4 : ℝ) • br e1 (br e1 (comb x1 x2 x3)) = x1 • e1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [comb, br, e1, e2, e3, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
    simp [Complex.ext_iff] <;> ring_nf

lemma proj2 (x1 x2 x3 : ℝ) :
    comb x1 x2 x3 + (1 / 4 : ℝ) • br e2 (br e2 (comb x1 x2 x3)) = x2 • e2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [comb, br, e1, e2, e3, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
    simp [Complex.ext_iff] <;> ring_nf

lemma proj3 (x1 x2 x3 : ℝ) :
    comb x1 x2 x3 + (1 / 4 : ℝ) • br e3 (br e3 (comb x1 x2 x3)) = x3 • e3 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [comb, br, e1, e2, e3, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
    simp [Complex.ext_iff] <;> ring_nf

/-- `su(2)` is simple. -/
theorem isSimpleLieAlg_su2 : IsSimpleLieAlg su2 := by
  refine ⟨⟨e1, e1_mem, e2, e2_mem, ?_⟩, ?_⟩
  · intro h
    have h' : br e1 e2 = 0 := h
    rw [br_e1_e2] at h'
    have := congrFun (congrFun h' 0) 1
    simp [e3] at this
  · intro V hVsub hVbr
    by_cases hV : V = ⊥
    · exact Or.inl hV
    right
    -- a non-zero element of V
    obtain ⟨Y, hYV, hY0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
    have hYsu := hVsub hYV
    have hbr : ∀ X ∈ su2, ∀ Z ∈ V, br X Z ∈ V := fun X hX Z hZ => hVbr X hX Z hZ
    -- the three components are in V
    set y1 := c1 Y
    set y2 := c2 Y
    set y3 := c3 Y
    have hYc : Y = comb y1 y2 y3 := eq_comb hYsu
    have m1 : y1 • e1 ∈ V := by
      rw [← proj1, ← hYc]
      exact V.add_mem hYV (V.smul_mem _ (hbr _ e1_mem _ (hbr _ e1_mem _ hYV)))
    have m2 : y2 • e2 ∈ V := by
      rw [← proj2 y1 y2 y3, ← hYc]
      exact V.add_mem hYV (V.smul_mem _ (hbr _ e2_mem _ (hbr _ e2_mem _ hYV)))
    have m3 : y3 • e3 ∈ V := by
      rw [← proj3 y1 y2 y3, ← hYc]
      exact V.add_mem hYV (V.smul_mem _ (hbr _ e3_mem _ (hbr _ e3_mem _ hYV)))
    -- one of the coefficients is non-zero, so a basis vector is in V
    have hsome : e1 ∈ V ∨ e2 ∈ V ∨ e3 ∈ V := by
      by_cases h1 : y1 = 0
      · by_cases h2 : y2 = 0
        · by_cases h3 : y3 = 0
          · exfalso; apply hY0; rw [hYc, h1, h2, h3]; simp [comb]
          · right; right
            have := V.smul_mem y3⁻¹ m3
            rwa [smul_smul, inv_mul_cancel₀ h3, one_smul] at this
        · right; left
          have := V.smul_mem y2⁻¹ m2
          rwa [smul_smul, inv_mul_cancel₀ h2, one_smul] at this
      · left
        have := V.smul_mem y1⁻¹ m1
        rwa [smul_smul, inv_mul_cancel₀ h1, one_smul] at this
    -- one basis vector generates the other two by brackets
    have half : ∀ {Z : Matrix (Fin 2) (Fin 2) ℂ}, (2 : ℝ) • Z ∈ V → Z ∈ V := by
      intro Z hZ
      have := V.smul_mem (1 / 2 : ℝ) hZ
      rwa [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at this
    have halfneg : ∀ {Z : Matrix (Fin 2) (Fin 2) ℂ}, -((2 : ℝ) • Z) ∈ V → Z ∈ V := by
      intro Z hZ
      exact half (by simpa using V.neg_mem hZ)
    have all3 : e1 ∈ V ∧ e2 ∈ V ∧ e3 ∈ V := by
      rcases hsome with h | h | h
      · have h3 : e3 ∈ V := halfneg (br_e2_e1 ▸ hbr e2 e2_mem e1 h)
        have h2 : e2 ∈ V := half (br_e3_e1 ▸ hbr e3 e3_mem e1 h)
        exact ⟨h, h2, h3⟩
      · have h3 : e3 ∈ V := half (br_e1_e2 ▸ hbr e1 e1_mem e2 h)
        have h1 : e1 ∈ V := halfneg (br_e3_e2 ▸ hbr e3 e3_mem e2 h)
        exact ⟨h1, h, h3⟩
      · have h1 : e1 ∈ V := half (br_e2_e3 ▸ hbr e2 e2_mem e3 h)
        have h2 : e2 ∈ V := halfneg (br_e1_e3 ▸ hbr e1 e1_mem e3 h)
        exact ⟨h1, h2, h⟩
    -- conclusion: su(2) ⊆ V
    apply Set.Subset.antisymm hVsub
    intro X hX
    rw [eq_comb hX]
    obtain ⟨h1, h2, h3⟩ := all3
    exact V.add_mem (V.add_mem (V.smul_mem _ h1) (V.smul_mem _ h2)) (V.smul_mem _ h3)

end SU2

end ClayYM
