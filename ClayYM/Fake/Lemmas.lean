/-
ClayYM/Fake/Lemmas.lean
=======================
Lemmas shared by the anti-vacuity guards:

* obstructions to FP1 (`UVTrace`): if `g(x) = |x|⁸ ⟨θ(x)θ(0)⟩_c` is bounded below by a constant
  `c > 0` near `0` (free-field-like behaviour of dimension ≥ 4, without logarithm), or bounded
  by `C |x|^α` (`α > 0`: behaviour of dimension < 4), or zero (θ ≡ 0: conformal theory), then
  `g(x) · log²|x|` cannot tend to a `K > 0`;
* bilinearity of `conn2` in the coefficient vectors;
* vanishing trace of the conformal structure, `ℐ_{μμ,ρσ}(u) = 0` for `|u| = 1`.
-/
import ClayYM.Statement

open MeasureTheory Filter Topology

noncomputable section

namespace ClayYM

/-! ### Behaviour of `log² |x|` near `0` -/

lemma tendsto_log_norm_atBot :
    Tendsto (fun x : Spacetime 4 => Real.log ‖x‖) (𝓝[≠] 0) atBot :=
  Real.tendsto_log_nhdsGT_zero.comp tendsto_norm_nhdsNE_zero

lemma tendsto_log_norm_sq :
    Tendsto (fun x : Spacetime 4 => (Real.log ‖x‖) ^ 2) (𝓝[≠] 0) atTop := by
  have h := (tendsto_pow_atTop (two_ne_zero)).comp (tendsto_neg_atBot_atTop.comp
    tendsto_log_norm_atBot)
  refine h.congr (fun x => ?_)
  simp [Function.comp]

lemma eventually_ne_lt (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x in 𝓝[≠] (0 : Spacetime 4), x ≠ 0 ∧ ‖x‖ < δ := by
  have h1 : ∀ᶠ x in 𝓝[≠] (0 : Spacetime 4), x ≠ 0 := self_mem_nhdsWithin
  have h2 : ∀ᶠ x in 𝓝[≠] (0 : Spacetime 4), x ∈ Metric.ball (0 : Spacetime 4) δ :=
    eventually_nhdsWithin_of_eventually_nhds (Metric.ball_mem_nhds 0 hδ)
  filter_upwards [h1, h2] with x hx1 hx2
  exact ⟨hx1, by simpa using hx2⟩

/-- Obstruction (lower bound): `c ≤ g` near `0` ⟹ `g · log²` does not converge. -/
lemma not_tendsto_of_lower_bound {g : Spacetime 4 → ℝ} {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hg : ∀ x : Spacetime 4, x ≠ 0 → ‖x‖ < δ → c ≤ g x) (K : ℝ) :
    ¬ Tendsto (fun x => g x * (Real.log ‖x‖) ^ 2) (𝓝[≠] 0) (𝓝 K) := by
  apply not_tendsto_nhds_of_tendsto_atTop
  have hev : ∀ᶠ x in 𝓝[≠] (0 : Spacetime 4),
      c * (Real.log ‖x‖) ^ 2 ≤ g x * (Real.log ‖x‖) ^ 2 := by
    filter_upwards [eventually_ne_lt δ hδ] with x hx
    exact mul_le_mul_of_nonneg_right (hg x hx.1 hx.2) (sq_nonneg _)
  exact tendsto_atTop_mono' _ hev (Tendsto.const_mul_atTop hc tendsto_log_norm_sq)

/-- Obstruction (power upper bound): `|g| ≤ C |x|^α` near `0` ⟹ `g · log² → 0`. -/
lemma tendsto_zero_of_upper_bound {g : Spacetime 4 → ℝ} {C α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (hg : ∀ x : Spacetime 4, x ≠ 0 → ‖x‖ < δ → |g x| ≤ C * ‖x‖ ^ α) :
    Tendsto (fun x => g x * (Real.log ‖x‖) ^ 2) (𝓝[≠] 0) (𝓝 0) := by
  have hlim : Tendsto (fun x : Spacetime 4 => C * (Real.log ‖x‖ * ‖x‖ ^ (α / 2)) ^ 2)
      (𝓝[≠] 0) (𝓝 0) := by
    have h1 := (tendsto_log_mul_rpow_nhdsGT_zero (half_pos hα)).comp
      (tendsto_norm_nhdsNE_zero (E := Spacetime 4))
    have h2 := (h1.pow 2).const_mul C
    simpa [Function.comp] using h2
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ne_lt δ hδ] with x hx
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hpow : (‖x‖ ^ (α / 2)) ^ 2 = ‖x‖ ^ α := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (Real.log ‖x‖)), mul_pow, hpow]
  have := hg x hx.1 hx.2
  calc |g x| * Real.log ‖x‖ ^ 2 ≤ (C * ‖x‖ ^ α) * Real.log ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right this (sq_nonneg _)
    _ = C * (Real.log ‖x‖ ^ 2 * ‖x‖ ^ α) := by ring

lemma not_tendsto_of_upper_bound {g : Spacetime 4 → ℝ} {C α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (hg : ∀ x : Spacetime 4, x ≠ 0 → ‖x‖ < δ → |g x| ≤ C * ‖x‖ ^ α) {K : ℝ} (hK : K ≠ 0) :
    ¬ Tendsto (fun x => g x * (Real.log ‖x‖) ^ 2) (𝓝[≠] 0) (𝓝 K) := fun h =>
  hK (tendsto_nhds_unique h (tendsto_zero_of_upper_bound hα hδ hg))

/-! ### Obstructions to FP1 (`UVTrace`) -/

/-- If `|x|⁸ ⟨θθ⟩_c ≥ c > 0` near `0`, FP1 fails (for every value `κ`). -/
theorem not_UVTrace_of_lower_bound (S : Schwinger YMIdx 4) (z₁ z₂ κ : ℝ) {c δ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ)
    (hg : ∀ x : Spacetime 4, x ≠ 0 → ‖x‖ < δ →
      c ≤ ‖x‖ ^ 8 * conn2 S (θc z₁ z₂) (θc z₁ z₂) x 0) :
    ¬ UVTrace S z₁ z₂ κ := by
  rintro ⟨h1, -⟩
  exact not_tendsto_of_lower_bound hc hδ hg κ h1

/-- If `||x|⁸ ⟨θθ⟩_c| ≤ C |x|^α` near `0` (`α > 0`), FP1 fails (for every `κ ≠ 0`). -/
theorem not_UVTrace_of_upper_bound (S : Schwinger YMIdx 4) (z₁ z₂ κ : ℝ) (hκ : κ ≠ 0)
    {C α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (hg : ∀ x : Spacetime 4, x ≠ 0 → ‖x‖ < δ →
      |‖x‖ ^ 8 * conn2 S (θc z₁ z₂) (θc z₁ z₂) x 0| ≤ C * ‖x‖ ^ α) :
    ¬ UVTrace S z₁ z₂ κ := by
  rintro ⟨h1, -⟩
  exact not_tendsto_of_upper_bound hα hδ hg hκ h1

/-- If `⟨θθ⟩_c ≡ 0` (scale-invariant / conformal theory: traceless `T`), FP1 fails. -/
theorem not_UVTrace_of_zero (S : Schwinger YMIdx 4) (z₁ z₂ κ : ℝ) (hκ : κ ≠ 0)
    (h0 : ∀ x : Spacetime 4, x ≠ 0 → conn2 S (θc z₁ z₂) (θc z₁ z₂) x 0 = 0) :
    ¬ UVTrace S z₁ z₂ κ := by
  refine not_UVTrace_of_upper_bound S z₁ z₂ κ hκ (C := 0) (α := 1) one_pos one_pos ?_
  intro x hx _
  simp [h0 x hx]

/-! ### Bilinearity of `conn2` -/

lemma S1_sum {κ : Type} [Fintype κ] (S : Schwinger YMIdx 4) (cs : κ → Coef)
    (x : Spacetime 4) (rest : LList YMIdx 4) :
    S1 S (fun a => ∑ q, cs q a) x rest = ∑ q, S1 S (cs q) x rest := by
  unfold S1
  simp_rw [Finset.sum_mul]
  exact Finset.sum_comm

lemma S2_sum_left {κ : Type} [Fintype κ] (S : Schwinger YMIdx 4) (cs : κ → Coef) (c' : Coef)
    (x y : Spacetime 4) :
    S2 S (fun a => ∑ q, cs q a) c' x y = ∑ q, S2 S (cs q) c' x y := by
  unfold S2
  calc ∑ a, ∑ b, (∑ q, cs q a) * c' b * S [(a, x), (b, y)]
      = ∑ a, ∑ b, ∑ q, cs q a * c' b * S [(a, x), (b, y)] := by
        simp only [Finset.sum_mul]
    _ = ∑ a, ∑ q, ∑ b, cs q a * c' b * S [(a, x), (b, y)] := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        exact Finset.sum_comm
    _ = ∑ q, ∑ a, ∑ b, cs q a * c' b * S [(a, x), (b, y)] := Finset.sum_comm

lemma S2_sum_right {κ : Type} [Fintype κ] (S : Schwinger YMIdx 4) (c : Coef) (cs : κ → Coef)
    (x y : Spacetime 4) :
    S2 S c (fun a => ∑ q, cs q a) x y = ∑ q, S2 S c (cs q) x y := by
  unfold S2
  calc ∑ a, ∑ b, c a * (∑ q, cs q b) * S [(a, x), (b, y)]
      = ∑ a, ∑ b, ∑ q, c a * cs q b * S [(a, x), (b, y)] := by
        simp only [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ a, ∑ q, ∑ b, c a * cs q b * S [(a, x), (b, y)] := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        exact Finset.sum_comm
    _ = ∑ q, ∑ a, ∑ b, c a * cs q b * S [(a, x), (b, y)] := Finset.sum_comm

lemma conn2_sum_left {κ : Type} [Fintype κ] (S : Schwinger YMIdx 4) (cs : κ → Coef) (c' : Coef)
    (x y : Spacetime 4) :
    conn2 S (fun a => ∑ q, cs q a) c' x y = ∑ q, conn2 S (cs q) c' x y := by
  unfold conn2
  rw [S2_sum_left S cs c' x y, S1_sum S cs x [], Finset.sum_mul, ← Finset.sum_sub_distrib]

lemma conn2_sum_right {κ : Type} [Fintype κ] (S : Schwinger YMIdx 4) (c : Coef) (cs : κ → Coef)
    (x y : Spacetime 4) :
    conn2 S c (fun a => ∑ q, cs q a) x y = ∑ q, conn2 S c (cs q) x y := by
  unfold conn2
  rw [S2_sum_right S c cs x y, S1_sum S cs y [], Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- `⟨θθ⟩_c = Σ_{μ,ρ} ⟨T_{μμ} T_{ρρ}⟩_c`. -/
lemma conn2_θc (S : Schwinger YMIdx 4) (z₁ z₂ : ℝ) (x y : Spacetime 4) :
    conn2 S (θc z₁ z₂) (θc z₁ z₂) x y =
      ∑ μ, ∑ ρ, conn2 S (Tc z₁ z₂ μ μ) (Tc z₁ z₂ ρ ρ) x y := by
  unfold θc
  rw [conn2_sum_left]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [conn2_sum_right]

/-! ### Trace of the conformal structure -/

/-- Algebraic identity: `Σ_μ ℐ_{μμ,ρσ}(u) = 4 u_ρ u_σ (|u|² − 1)` (in coordinates). -/
lemma sum_confI_diag (u : Spacetime 4) (ρ σ : Fin 4) :
    ∑ μ, confI u μ μ ρ σ = 4 * u ρ * u σ * (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 - 1) := by
  fin_cases ρ <;> fin_cases σ <;> simp [confI, invI, kd, Fin.sum_univ_four] <;> ring

lemma norm_sq_coords (u : Spacetime 4) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  simp [Fin.sum_univ_four, Real.norm_eq_abs, sq_abs]

/-- For `|u| = 1`, the conformal structure is traceless: `Σ_μ ℐ_{μμ,ρσ}(u) = 0`. -/
theorem confI_traceless {u : Spacetime 4} (hu : ‖u‖ = 1) (ρ σ : Fin 4) :
    ∑ μ, confI u μ μ ρ σ = 0 := by
  rw [sum_confI_diag]
  have h := norm_sq_coords u
  rw [hu] at h
  rw [← h]
  ring

end ClayYM
