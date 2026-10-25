/-
ClayYM/Fake/HiddenVacuum.lean
============================
FAKE MODEL: a hidden vacuum in an invisible sector, the mechanism of O ⊗ I.
The transfer Hamiltonian on real Euclidean three-space has eigenvalues 0, 1, 0.
The visible algebra A₀ contains the vacuum e₀ and the excitation e₁, but cannot see e₂.
Its q-form holds although the full space has neither a mass gap nor a unique vacuum.

Thus a q-form on a non-cyclic algebra does not imply either conclusion: the density
hypothesis in `Recon.massGapOn_of_qGapOn` and `Recon.vacuum_unique` is indispensable.
Uniqueness of the vacuum is not an additional hypothesis: it follows from the q-form
and density, as proved in `Transfer.lean`.
-/
import ClayYM.Transfer

open scoped RealInnerProductSpace

noncomputable section

namespace ClayYM.HiddenVacuum

open Transfer

abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

def e (i : Fin 3) : E3 := EuclideanSpace.single i 1

/-- e^{-tH} with H e₀ = 0 (vacuum), H e₁ = e₁ (visible excitation),
and H e₂ = 0 (a second, hidden vacuum). -/
def T (t : ℝ) : E3 →L[ℝ] E3 :=
  ContinuousLinearMap.id ℝ E3 -
    (1 - Real.exp (-t)) • (innerSL ℝ (e 1)).smulRight (e 1)

def ops : VecOps E3 := ⟨(· + ·), (· • ·), e 0⟩

def B (v w : E3) (t : ℝ) : ℝ := ⟪v, T t w⟫

/-- The visible algebra does not see mode 2. -/
def A0 : Set E3 := {v | v 2 = 0}

@[simp] lemma e_apply (i j : Fin 3) : e i j = if j = i then 1 else 0 := by
  simp [e, PiLp.single_apply]

@[simp] lemma inner_e_left (i : Fin 3) (x : E3) : ⟪e i, x⟫ = x i := by
  simp [e, EuclideanSpace.inner_single_left]

@[simp] lemma inner_e_right (x : E3) (i : Fin 3) : ⟪x, e i⟫ = x i := by
  rw [real_inner_comm, inner_e_left]

@[simp] lemma norm_e (i : Fin 3) : ‖e i‖ = 1 := by
  simp [e]

lemma T_apply (t : ℝ) (x : E3) :
    T t x = x - ((1 - Real.exp (-t)) * ⟪e 1, x⟫) • e 1 := by
  simp [T, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]

@[simp] lemma T_zero (x : E3) : T 0 x = x := by
  simp [T_apply]

@[simp] lemma T_e0 (t : ℝ) : T t (e 0) = e 0 := by
  simp [T_apply]

@[simp] lemma T_e1 (t : ℝ) : T t (e 1) = Real.exp (-t) • e 1 := by
  rw [T_apply]
  simp only [inner_e_left, e_apply, ite_true, mul_one]
  have h : (1 : ℝ) - (1 - Real.exp (-t)) = Real.exp (-t) := by ring
  simpa only [sub_smul, one_smul] using congrArg (fun c : ℝ => c • e 1) h

@[simp] lemma T_e2 (t : ℝ) : T t (e 2) = e 2 := by
  simp [T_apply]

lemma T_add (s t : ℝ) : T (s + t) = (T s).comp (T t) := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply, T_apply, inner_e_left,
    PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, e_apply]
  by_cases hi : i = 1
  · subst i
    simp only [ite_true]
    rw [neg_add, Real.exp_add]
    ring
  · simp [hi]

lemma T_symm (t : ℝ) (x y : E3) : ⟪T t x, y⟫ = ⟪x, T t y⟫ := by
  simp only [T_apply, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, inner_e_left, inner_e_right]
  ring

lemma norm_sub_projection_sq (x : E3) (c : ℝ) :
    ‖x - (c * ⟪e 1, x⟫) • e 1‖ ^ 2 =
      ‖x‖ ^ 2 - c * (2 - c) * ⟪e 1, x⟫ ^ 2 := by
  rw [norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    norm_e, real_inner_smul_right, inner_e_right, inner_e_left]
  ring

lemma T_contr (t : ℝ) (ht : 0 ≤ t) : ‖T t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have he0 := (Real.exp_pos (-t)).le
  have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hc0 : 0 ≤ 1 - Real.exp (-t) := by linarith
  have hc1 : 1 - Real.exp (-t) ≤ 1 := by linarith
  have hp : 0 ≤ (1 - Real.exp (-t)) * (2 - (1 - Real.exp (-t))) * ⟪e 1, x⟫ ^ 2 :=
    mul_nonneg (mul_nonneg hc0 (by linarith)) (sq_nonneg _)
  have hs : ‖T t x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [T_apply, norm_sub_projection_sq]
    linarith
  simpa only [one_mul] using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

def recon : Recon ops B where
  H := E3
  cls := id
  T := T
  inner_cls := by intro F G; simp [B]
  inner_T := by intro F G t _; rfl
  T_add := by intro s t _ _; exact T_add s t
  T_symm := by intro t _ x y; exact T_symm t x y
  T_contr := T_contr
  T_vac := by intro t _; exact T_e0 t
  dense := Function.Surjective.denseRange (fun x => ⟨x, rfl⟩)

theorem isBilin : IsBilin ops B where
  add_left := by intro F F' G t; simp [B, ops, inner_add_left]
  add_right := by intro F G G' t; simp [B, ops, inner_add_right]
  smul_left := by intro c F G t; simp [B, ops, real_inner_smul_left]
  smul_right := by intro c F G t; simp [B, ops, real_inner_smul_right]

theorem B_vac : B (e 0) (e 0) 0 = 1 := by
  simp [B]

lemma trunc_visible (v : E3) (hv : v ∈ A0) : ops.trunc B v = v 1 • e 1 := by
  have hv2 : v 2 = 0 := hv
  ext i
  fin_cases i <;> simp [VecOps.trunc, ops, B, hv2]

theorem qGap {ℓ : ℝ} (hℓ : 0 < ℓ) : QGapOn ops B A0 ℓ (Real.exp (-ℓ)) := by
  refine ⟨hℓ, Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith), ?_⟩
  intro v hv
  rw [trunc_visible v hv]
  simp only [B, map_smul, T_e1, real_inner_smul_left,
    real_inner_smul_right, inner_e_left, e_apply, ite_true, neg_zero, Real.exp_zero]
  exact le_of_eq (by ring)

theorem not_massGap (Δ : ℝ) : ¬ MassGapOn ops B Set.univ Δ := by
  intro h
  have hb := h.2 (e 2) (Set.mem_univ _) (e 2) (Set.mem_univ _) 1 (by norm_num)
  have he : Real.exp (-Δ) < 1 := Real.exp_lt_one_iff.mpr (by linarith [h.1])
  have hb' : 1 ≤ Real.exp (-Δ) := by
    simpa [B, ops] using hb
  exact (not_le_of_gt he) hb'

theorem second_vacuum {ℓ : ℝ} (_hℓ : 0 ≤ ℓ) :
    recon.T ℓ (e 2) = e 2 ∧ e 2 ≠ ⟪recon.ω, e 2⟫ • recon.ω := by
  constructor
  · exact T_e2 ℓ
  · change e 2 ≠ ⟪e 0, e 2⟫ • e 0
    intro h
    have hc := congrArg (fun x : E3 => x 2) h
    simp at hc

theorem density_needed : ¬ ∀ (V : Type) (o : VecOps V) (B : V → V → ℝ → ℝ)
    (_ : Recon o B) (𝒜₀ : Set V) (ℓ q : ℝ), B o.Ω o.Ω 0 = 1 →
    QGapOn o B 𝒜₀ ℓ q → MassGapOn o B Set.univ (-Real.log q / ℓ) := by
  intro h
  exact not_massGap _ (h E3 ops B recon A0 1 (Real.exp (-1)) B_vac (qGap (by norm_num)))

theorem uniqueness_needs_density : ¬ ∀ (V : Type) (o : VecOps V)
    (B : V → V → ℝ → ℝ) (r : Recon o B) (𝒜₀ : Set V) (ℓ q : ℝ),
    B o.Ω o.Ω 0 = 1 → QGapOn o B 𝒜₀ ℓ q →
    ∀ w : r.H, r.T ℓ w = w → w = ⟪r.ω, w⟫ • r.ω := by
  intro h
  have hv := second_vacuum (ℓ := 1) (by norm_num)
  exact hv.2 (h E3 ops B recon A0 1 (Real.exp (-1)) B_vac (qGap (by norm_num)) (e 2) hv.1)

end ClayYM.HiddenVacuum
