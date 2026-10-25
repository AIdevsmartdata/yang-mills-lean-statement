/-
ClayYM/Fake/HeatKernel.lean
===========================
The massive free field (GFF) in dimension 4: its two-point function is the Green kernel of
`−Δ + m²`, in proper-time (heat-kernel) representation:
  `C_m(x) = ∫₀^∞ (4πs)^{-2} exp(−|x|²/(4s) − m² s) ds`.
We prove the canonical dimension-1 bounds for `0 < |x| ≤ 1`:
  `c₁/|x|² ≤ C_m(x) ≤ c₂/|x|²`, with `c₁ = e^{−1/4 − 2m²}/(64π²)` and `c₂ = 2/π² + 1/(16π²)`,
then instantiate the guard `wick_not_UVTrace`: every theory whose `⟨θθ⟩_c` is that of a Wick
polynomial (without derivatives) of the massive free field — whatever the mass `m` — violates FP1.
-/
import ClayYM.Fake.FreeScalar

open MeasureTheory Set Filter Real

noncomputable section

namespace ClayYM

/-- Proper-time integrand `(16π²)⁻¹ s^{-2} exp(−r²/(4s) − m²s)`. -/
def hk (m r s : ℝ) : ℝ := (16 * π ^ 2)⁻¹ * s ^ (-2 : ℝ) * Real.exp (-(r ^ 2 / (4 * s)) - m ^ 2 * s)

/-- Two-point function of the free field of mass `m` in dimension 4. -/
def gffKernel (m : ℝ) (x : Spacetime 4) : ℝ := ∫ s in Ioi (0 : ℝ), hk m ‖x‖ s

lemma rpow_neg_two' {s : ℝ} (hs : 0 < s) : s ^ (-2 : ℝ) = (s ^ 2)⁻¹ := by
  rw [Real.rpow_neg hs.le]
  norm_cast

lemma hk_nonneg (m r : ℝ) {s : ℝ} (hs : 0 < s) : 0 ≤ hk m r s := by
  unfold hk
  have : 0 ≤ s ^ (-2 : ℝ) := Real.rpow_nonneg hs.le _
  positivity

lemma hk_le_tail (m r : ℝ) {s : ℝ} (hs : 0 < s) : hk m r s ≤ (16 * π ^ 2)⁻¹ * s ^ (-2 : ℝ) := by
  unfold hk
  have hle : Real.exp (-(r ^ 2 / (4 * s)) - m ^ 2 * s) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have h1 : 0 ≤ r ^ 2 / (4 * s) := by positivity
    have h2 : 0 ≤ m ^ 2 * s := by positivity
    linarith
  have hpos : 0 ≤ (16 * π ^ 2)⁻¹ * s ^ (-2 : ℝ) := by
    have : 0 ≤ s ^ (-2 : ℝ) := Real.rpow_nonneg hs.le _
    positivity
  calc (16 * π ^ 2)⁻¹ * s ^ (-2 : ℝ) * Real.exp (-(r ^ 2 / (4 * s)) - m ^ 2 * s)
      ≤ (16 * π ^ 2)⁻¹ * s ^ (-2 : ℝ) * 1 := mul_le_mul_of_nonneg_left hle hpos
    _ = (16 * π ^ 2)⁻¹ * s ^ (-2 : ℝ) := mul_one _

lemma exp_neg_le_two_div_sq {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 2 / y ^ 2 := by
  have h := Real.quadratic_le_exp_of_nonneg hy.le
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos y) (by positivity)]
  nlinarith [sq_nonneg y]

lemma hk_le_head (m : ℝ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) : hk m r s ≤ 2 / (π ^ 2 * r ^ 4) := by
  unfold hk
  rw [rpow_neg_two' hs]
  have hy : 0 < r ^ 2 / (4 * s) := by positivity
  have h1 : Real.exp (-(r ^ 2 / (4 * s)) - m ^ 2 * s) ≤ Real.exp (-(r ^ 2 / (4 * s))) := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ m ^ 2 * s := by positivity
    linarith
  have h2 := exp_neg_le_two_div_sq hy
  have hpos : 0 ≤ (16 * π ^ 2)⁻¹ * (s ^ 2)⁻¹ := by positivity
  calc (16 * π ^ 2)⁻¹ * (s ^ 2)⁻¹ * Real.exp (-(r ^ 2 / (4 * s)) - m ^ 2 * s)
      ≤ (16 * π ^ 2)⁻¹ * (s ^ 2)⁻¹ * (2 / (r ^ 2 / (4 * s)) ^ 2) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hpos
    _ = 2 / (π ^ 2 * r ^ 4) := by
        field_simp
        ring

lemma hk_ge_mid (m : ℝ) {r s : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hs1 : r ^ 2 ≤ s)
    (hs2 : s ≤ 2 * r ^ 2) :
    Real.exp (-(1 / 4) - 2 * m ^ 2) / (64 * π ^ 2 * r ^ 4) ≤ hk m r s := by
  have hr2 : 0 < r ^ 2 := by positivity
  have hs : 0 < s := lt_of_lt_of_le hr2 hs1
  unfold hk
  rw [rpow_neg_two' hs]
  have hexp : Real.exp (-(1 / 4) - 2 * m ^ 2) ≤ Real.exp (-(r ^ 2 / (4 * s)) - m ^ 2 * s) := by
    apply Real.exp_le_exp.mpr
    have ha : r ^ 2 / (4 * s) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hb : m ^ 2 * s ≤ 2 * m ^ 2 := by
      have hs' : s ≤ 2 := by nlinarith
      nlinarith [sq_nonneg m]
    linarith
  have hinv : (4 * r ^ 4)⁻¹ ≤ (s ^ 2)⁻¹ := by
    apply inv_anti₀ (by positivity)
    nlinarith
  calc Real.exp (-(1 / 4) - 2 * m ^ 2) / (64 * π ^ 2 * r ^ 4)
      = (16 * π ^ 2)⁻¹ * (4 * r ^ 4)⁻¹ * Real.exp (-(1 / 4) - 2 * m ^ 2) := by
        field_simp
        ring
    _ ≤ (16 * π ^ 2)⁻¹ * (s ^ 2)⁻¹ * Real.exp (-(r ^ 2 / (4 * s)) - m ^ 2 * s) := by
        gcongr

lemma continuousOn_hk (m r : ℝ) : ContinuousOn (hk m r) (Ioi 0) := by
  unfold hk
  apply ContinuousOn.mul
  · apply ContinuousOn.mul continuousOn_const
    exact ContinuousOn.rpow_const continuousOn_id (fun s hs => Or.inl (ne_of_gt hs))
  · apply Real.continuous_exp.comp_continuousOn
    apply ContinuousOn.sub
    · apply ContinuousOn.neg
      apply ContinuousOn.div continuousOn_const (continuousOn_const.mul continuousOn_id)
      intro s hs
      have hs' : (0 : ℝ) < s := hs
      exact mul_ne_zero (by norm_num) (ne_of_gt hs')
    · exact continuousOn_const.mul continuousOn_id

lemma integrableOn_hk (m : ℝ) {r : ℝ} (hr : 0 < r) : IntegrableOn (hk m r) (Ioi 0) := by
  have hr2 : 0 < r ^ 2 := by positivity
  have hmeas : AEStronglyMeasurable (hk m r) (volume.restrict (Ioi 0)) :=
    (continuousOn_hk m r).aestronglyMeasurable measurableSet_Ioi
  have h1 : IntegrableOn (hk m r) (Ioc 0 (r ^ 2)) := by
    refine IntegrableOn.of_bound (by simp [Real.volume_Ioc])
      (hmeas.mono_measure (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl))
      (2 / (π ^ 2 * r ^ 4)) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall (fun s hs => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hk_nonneg m r hs.1)]
    exact hk_le_head m hr hs.1
  have h2 : IntegrableOn (hk m r) (Ioi (r ^ 2)) := by
    have hint := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hr2).const_mul
      ((16 * π ^ 2)⁻¹)
    refine hint.mono' (hmeas.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi hr2.le) le_rfl)) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun s hs => ?_))
    have hs0 : 0 < s := lt_trans hr2 hs
    rw [Real.norm_eq_abs, abs_of_nonneg (hk_nonneg m r hs0)]
    exact hk_le_tail m r hs0
  have := h1.union h2
  rwa [Ioc_union_Ioi_eq_Ioi hr2.le] at this

/-- Canonical lower bound: `C_m(x) ≥ c₁/|x|²` for `0 < |x| ≤ 1`. -/
lemma gffKernel_lower (m : ℝ) {x : Spacetime 4} (hx : x ≠ 0) (hx1 : ‖x‖ ≤ 1) :
    Real.exp (-(1 / 4) - 2 * m ^ 2) / (64 * π ^ 2) / ‖x‖ ^ 2 ≤ gffKernel m x := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set r := ‖x‖ with hrdef
  have hr2 : 0 < r ^ 2 := by positivity
  unfold gffKernel
  rw [← hrdef]
  have hsub : Icc (r ^ 2) (2 * r ^ 2) ⊆ Ioi 0 := fun s hs => lt_of_lt_of_le hr2 hs.1
  have hI := integrableOn_hk m hr
  have hvol : volume.real (Icc (r ^ 2) (2 * r ^ 2)) = r ^ 2 := by
    rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  calc Real.exp (-(1 / 4) - 2 * m ^ 2) / (64 * π ^ 2) / r ^ 2
      = volume.real (Icc (r ^ 2) (2 * r ^ 2)) •
          (Real.exp (-(1 / 4) - 2 * m ^ 2) / (64 * π ^ 2 * r ^ 4)) := by
        rw [hvol, smul_eq_mul]
        field_simp
    _ ≤ ∫ s in Icc (r ^ 2) (2 * r ^ 2), hk m r s :=
        setIntegral_ge_of_const_le measurableSet_Icc (by simp [Real.volume_Icc])
          (fun s hs => hk_ge_mid m hr hx1 hs.1 hs.2) (hI.mono_set hsub)
    _ ≤ ∫ s in Ioi 0, hk m r s := by
        apply setIntegral_mono_set hI
        · exact (ae_restrict_iff' measurableSet_Ioi).mpr
            (Eventually.of_forall (fun s hs => hk_nonneg m r hs))
        · exact hsub.eventuallyLE

/-- Canonical upper bound: `C_m(x) ≤ c₂/|x|²` for `x ≠ 0`. -/
lemma gffKernel_upper (m : ℝ) {x : Spacetime 4} (hx : x ≠ 0) :
    gffKernel m x ≤ (2 / π ^ 2 + (16 * π ^ 2)⁻¹) / ‖x‖ ^ 2 := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set r := ‖x‖ with hrdef
  have hr2 : 0 < r ^ 2 := by positivity
  unfold gffKernel
  rw [← hrdef]
  have hI := integrableOn_hk m hr
  rw [← Ioc_union_Ioi_eq_Ioi hr2.le,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hI.mono_set Ioc_subset_Ioi_self) (hI.mono_set (Ioi_subset_Ioi hr2.le))]
  have hA : ∫ s in Ioc 0 (r ^ 2), hk m r s ≤ 2 / (π ^ 2 * r ^ 2) := by
    calc ∫ s in Ioc 0 (r ^ 2), hk m r s
        ≤ ∫ _s in Ioc 0 (r ^ 2), 2 / (π ^ 2 * r ^ 4) :=
          setIntegral_mono_on (hI.mono_set Ioc_subset_Ioi_self)
            (integrableOn_const (by simp [Real.volume_Ioc])) measurableSet_Ioc
            (fun s hs => hk_le_head m hr hs.1)
      _ = 2 / (π ^ 2 * r ^ 2) := by
          rw [setIntegral_const, measureReal_def, Real.volume_Ioc,
            ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
          field_simp
          ring
  have hB : ∫ s in Ioi (r ^ 2), hk m r s ≤ (16 * π ^ 2)⁻¹ / r ^ 2 := by
    have hint := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hr2).const_mul
      ((16 * π ^ 2)⁻¹)
    calc ∫ s in Ioi (r ^ 2), hk m r s
        ≤ ∫ s in Ioi (r ^ 2), (16 * π ^ 2)⁻¹ * s ^ (-2 : ℝ) :=
          setIntegral_mono_on (hI.mono_set (Ioi_subset_Ioi hr2.le)) hint measurableSet_Ioi
            (fun s hs => hk_le_tail m r (lt_trans hr2 hs))
      _ = (16 * π ^ 2)⁻¹ / r ^ 2 := by
          rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hr2]
          rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
          field_simp
  calc (∫ s in Ioc 0 (r ^ 2), hk m r s) + ∫ s in Ioi (r ^ 2), hk m r s
      ≤ 2 / (π ^ 2 * r ^ 2) + (16 * π ^ 2)⁻¹ / r ^ 2 := add_le_add hA hB
    _ = (2 / π ^ 2 + (16 * π ^ 2)⁻¹) / r ^ 2 := by
        field_simp

/-- **Instantiated "massive free field" guard**: for every mass `m`, every theory whose connected
two-point function of `θ` is that of a Wick polynomial (without derivatives) of the free field of
mass `m` in dimension 4 violates FP1. -/
theorem gff_wick_not_UVTrace (S : Schwinger YMIdx 4) (z₁ z₂ κ : ℝ) (hκ : κ ≠ 0) (m : ℝ) (D : ℕ)
    (w : ℕ → ℝ)
    (hθ : ∀ x : Spacetime 4, x ≠ 0 → conn2 S (θc z₁ z₂) (θc z₁ z₂) x 0 =
      ∑ k ∈ Finset.range (D + 1), (w k) ^ 2 * (k.factorial : ℝ) * (gffKernel m x) ^ k) :
    ¬ UVTrace S z₁ z₂ κ := by
  refine wick_not_UVTrace S z₁ z₂ κ hκ (gffKernel m)
    (c₁ := Real.exp (-(1 / 4) - 2 * m ^ 2) / (64 * π ^ 2))
    (c₂ := 2 / π ^ 2 + (16 * π ^ 2)⁻¹) (by positivity) (by positivity)
    (fun x hx hx1 => gffKernel_lower m hx hx1) (fun x hx _ => gffKernel_upper m hx) D w hθ

end ClayYM
