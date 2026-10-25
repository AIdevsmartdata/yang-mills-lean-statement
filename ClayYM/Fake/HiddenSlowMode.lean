/-
ClayYM/Fake/HiddenSlowMode.lean
============================
FAKE MODEL (abstract transfer model, NOT a model of Schwinger kernels): a unique vacuum with an
invisible slow mode. The transfer Hamiltonian on real Euclidean three-space is diag(0, 1, 1/2).
The q-form holds on the non-cyclic visible subspace A₀ = {v | v 2 = 0}, with q = exp(-ℓ), but
the claimed mass gap -log(q)/ℓ = 1 fails because the hidden mode decays at rate 1/2.
Adding uniqueness of the vacuum therefore does not replace the density hypothesis.
-/
import ClayYM.Fake.HiddenVacuum

open Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace ClayYM.HiddenSlowMode

open Transfer ClayYM.HiddenVacuum

/-- e^{-tH}, H = diag(0, 1, 1/2). -/
def T2 (t : ℝ) : E3 →L[ℝ] E3 :=
  ContinuousLinearMap.id ℝ E3 - (1 - Real.exp (-t)) • (innerSL ℝ (e 1)).smulRight (e 1)
    - (1 - Real.exp (-(t / 2))) • (innerSL ℝ (e 2)).smulRight (e 2)

def B2 (v w : E3) (t : ℝ) : ℝ := ⟪v, T2 t w⟫

lemma T2_apply (t : ℝ) (x : E3) :
    T2 t x = x - ((1 - Real.exp (-t)) * ⟪e 1, x⟫) • e 1
      - ((1 - Real.exp (-(t / 2))) * ⟪e 2, x⟫) • e 2 := by
  simp [T2, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]

@[simp] lemma T2_zero (x : E3) : T2 0 x = x := by
  simp [T2_apply]

@[simp] lemma T2_e0 (t : ℝ) : T2 t (e 0) = e 0 := by
  simp [T2_apply]

@[simp] lemma T2_e1 (t : ℝ) : T2 t (e 1) = Real.exp (-t) • e 1 := by
  ext i
  fin_cases i <;> simp [T2_apply]

@[simp] lemma T2_e2 (t : ℝ) : T2 t (e 2) = Real.exp (-(t / 2)) • e 2 := by
  ext i
  fin_cases i <;> simp [T2_apply]

lemma T2_add (s t : ℝ) : T2 (s + t) = (T2 s).comp (T2 t) := by
  ext x i
  fin_cases i <;>
    simp [ContinuousLinearMap.comp_apply, T2_apply, add_div, Real.exp_add] <;> ring

lemma T2_symm (t : ℝ) (x y : E3) : ⟪T2 t x, y⟫ = ⟪x, T2 t y⟫ := by
  simp only [T2_apply, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, inner_e_left, inner_e_right]
  ring

lemma norm_sub_two_projections_sq (x : E3) (c₁ c₂ : ℝ) :
    ‖x - (c₁ * ⟪e 1, x⟫) • e 1 - (c₂ * ⟪e 2, x⟫) • e 2‖ ^ 2 =
      ‖x‖ ^ 2 - c₁ * (2 - c₁) * ⟪e 1, x⟫ ^ 2
        - c₂ * (2 - c₂) * ⟪e 2, x⟫ ^ 2 := by
  rw [norm_sub_sq_real, norm_sub_projection_sq]
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_e,
    inner_sub_left, real_inner_smul_left, real_inner_smul_right,
    inner_e_left, inner_e_right, e_apply]
  norm_num
  ring

lemma T2_contr (t : ℝ) (ht : 0 ≤ t) : ‖T2 t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have he₁ := (Real.exp_pos (-t)).le
  have he₂ := (Real.exp_pos (-(t / 2))).le
  have hb₁ : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hb₂ : Real.exp (-(t / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hp₁ : 0 ≤ (1 - Real.exp (-t)) * (2 - (1 - Real.exp (-t))) * ⟪e 1, x⟫ ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)
  have hp₂ : 0 ≤ (1 - Real.exp (-(t / 2))) * (2 - (1 - Real.exp (-(t / 2)))) *
      ⟪e 2, x⟫ ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)
  have hs : ‖T2 t x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [T2_apply, norm_sub_two_projections_sq]
    linarith
  simpa only [one_mul] using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

def recon2 : Recon ops B2 where
  H := E3
  cls := id
  T := T2
  inner_cls := by intro F G; simp [B2]
  inner_T := by intro F G t _; rfl
  T_add := by intro s t _ _; exact T2_add s t
  T_symm := by intro t _ x y; exact T2_symm t x y
  T_contr := T2_contr
  T_vac := by intro t _; exact T2_e0 t
  T_cont := by
    intro x
    have hc : Continuous fun t : ℝ => T2 t x := by
      simp only [T2_apply]
      fun_prop
    have h := hc.tendsto 0
    rw [T2_zero] at h
    exact tendsto_nhdsWithin_of_tendsto_nhds h
  dense := Function.Surjective.denseRange (fun x => ⟨x, rfl⟩)

theorem isBilin2 : IsBilin ops B2 where
  add_left := by intro F F' G t; simp [B2, ops, inner_add_left]
  add_right := by intro F G G' t; simp [B2, ops, inner_add_right]
  smul_left := by intro c F G t; simp [B2, ops, real_inner_smul_left]
  smul_right := by intro c F G t; simp [B2, ops, real_inner_smul_right]

theorem B2_vac : B2 (e 0) (e 0) 0 = 1 := by
  simp [B2]

lemma trunc_visible2 (v : E3) (hv : v ∈ A0) : ops.trunc B2 v = v 1 • e 1 := by
  have hv2 : v 2 = 0 := hv
  ext i
  fin_cases i <;> simp [VecOps.trunc, ops, B2, hv2]

theorem qGap2 {ℓ : ℝ} (hℓ : 0 < ℓ) : QGapOn ops B2 A0 ℓ (Real.exp (-ℓ)) := by
  refine ⟨hℓ, Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith), ?_⟩
  intro v hv
  rw [trunc_visible2 v hv]
  simp only [B2, map_smul, T2_e1, real_inner_smul_left,
    real_inner_smul_right, inner_e_left, e_apply, ite_true, neg_zero, Real.exp_zero]
  exact le_of_eq (by ring)

theorem vacuum_unique2 {ℓ : ℝ} (hℓ : 0 < ℓ) (w : E3) (hw : recon2.T ℓ w = w) :
    w = ⟪recon2.ω, w⟫ • recon2.ω := by
  have he₁ : Real.exp (-ℓ) ≠ 1 := ne_of_lt (Real.exp_lt_one_iff.mpr (by linarith))
  have he₂ : Real.exp (-(ℓ / 2)) ≠ 1 := ne_of_lt (Real.exp_lt_one_iff.mpr (by linarith))
  have h₁ := congrArg (fun x : E3 => x 1) hw
  have h₂ := congrArg (fun x : E3 => x 2) hw
  change (T2 ℓ w) 1 = w 1 at h₁
  change (T2 ℓ w) 2 = w 2 at h₂
  simp [T2_apply] at h₁ h₂
  have hz₁ : w 1 = 0 := h₁.resolve_left (sub_ne_zero.mpr he₁.symm)
  have hz₂ : w 2 = 0 := h₂.resolve_left (sub_ne_zero.mpr he₂.symm)
  change w = ⟪e 0, w⟫ • e 0
  ext i
  fin_cases i <;> simp [hz₁, hz₂]

theorem not_massGap_one : ¬ MassGapOn ops B2 Set.univ 1 := by
  intro h
  have hb := h.2 (e 2) (Set.mem_univ _) (e 2) (Set.mem_univ _) 1 (by norm_num)
  have hb' : Real.exp (-(1 / 2 : ℝ)) ≤ Real.exp (-1) := by
    simpa [B2, ops, real_inner_smul_right, abs_of_pos (Real.exp_pos _)] using hb
  have he : Real.exp (-1 : ℝ) < Real.exp (-(1 / 2 : ℝ)) :=
    Real.exp_lt_exp.mpr (by norm_num)
  exact (not_le_of_gt he) hb'

theorem density_needed_unique_vacuum : ¬ ∀ (V : Type) (o : VecOps V)
    (B : V → V → ℝ → ℝ) (r : Recon o B) (𝒜₀ : Set V) (ℓ q : ℝ),
    B o.Ω o.Ω 0 = 1 →
    (∀ w : r.H, r.T ℓ w = w → w = ⟪r.ω, w⟫ • r.ω) →
    QGapOn o B 𝒜₀ ℓ q → MassGapOn o B Set.univ (-Real.log q / ℓ) := by
  intro h
  have hg := h E3 ops B2 recon2 A0 1 (Real.exp (-1)) B2_vac
    (vacuum_unique2 (by norm_num)) (qGap2 (by norm_num))
  apply not_massGap_one
  simpa only [Real.log_exp, neg_neg, div_one] using hg

end ClayYM.HiddenSlowMode
