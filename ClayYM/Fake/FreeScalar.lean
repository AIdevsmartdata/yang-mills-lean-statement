/-
ClayYM/Fake/FreeScalar.lean
===========================
FAKE MODEL: the free scalar field (Gaussian, massive or massless) in dimension 4, with an arbitrary
"SU(2) label" (a negative witness). For a free field `φ` with two-point function
`C(x)`, and `θ = Σ_k w_k :φ^k:` a Wick polynomial (without derivatives), the Wick identity gives
`⟨θ(x) θ(0)⟩_c = Σ_k w_k² k! C(x)^k` (orthogonality of Wick powers; checked by enumerating
the contractions for k ≤ 6 in `constants/sympy_constantes.py`, not formalised here).

Proved guard (`wick_not_UVTrace`): if `C` has the canonical dimension-1 behaviour
`c₁/|x|² ≤ C(x) ≤ c₂/|x|²` for `0 < |x| ≤ 1` (true for the massive or massless free field in 4D),
then FP1 FAILS for EVERY such polynomial: either a degree `k ≥ 4` is present and `|x|⁸⟨θθ⟩ ≥ c > 0`
(no logarithm: `·log²` diverges), or all degrees are `≤ 3` and `|x|⁸⟨θθ⟩ ≤ M |x|²`.
-/
import ClayYM.Fake.Lemmas

open MeasureTheory Filter Topology

noncomputable section

namespace ClayYM

/-- **"Free field" guard.** -/
theorem wick_not_UVTrace (S : Schwinger YMIdx 4) (z₁ z₂ κ : ℝ) (hκ : κ ≠ 0)
    (C : Spacetime 4 → ℝ) {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 ≤ c₂)
    (hlow : ∀ x : Spacetime 4, x ≠ 0 → ‖x‖ ≤ 1 → c₁ / ‖x‖ ^ 2 ≤ C x)
    (hup : ∀ x : Spacetime 4, x ≠ 0 → ‖x‖ ≤ 1 → C x ≤ c₂ / ‖x‖ ^ 2)
    (D : ℕ) (w : ℕ → ℝ)
    (hθ : ∀ x : Spacetime 4, x ≠ 0 → conn2 S (θc z₁ z₂) (θc z₁ z₂) x 0 =
      ∑ k ∈ Finset.range (D + 1), (w k) ^ 2 * (k.factorial : ℝ) * (C x) ^ k) :
    ¬ UVTrace S z₁ z₂ κ := by
  by_cases hbig : ∃ k ∈ Finset.range (D + 1), 4 ≤ k ∧ w k ≠ 0
  · -- a degree k₀ ≥ 4: lower bound by a strictly positive constant
    obtain ⟨k₀, hk₀, h4, hw⟩ := hbig
    have hcpos : 0 < (w k₀) ^ 2 * (k₀.factorial : ℝ) * c₁ ^ k₀ := by
      have : 0 < (w k₀) ^ 2 := by positivity
      positivity
    refine not_UVTrace_of_lower_bound S z₁ z₂ κ hcpos one_pos ?_
    intro x hx hx1
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hr1 : ‖x‖ ≤ 1 := hx1.le
    have hClow := hlow x hx hr1
    have hCpos : 0 < C x := lt_of_lt_of_le (by positivity) hClow
    rw [hθ x hx]
    have hterm_nonneg : ∀ k ∈ Finset.range (D + 1),
        0 ≤ (w k) ^ 2 * (k.factorial : ℝ) * (C x) ^ k := fun k _ => by positivity
    have hsingle : (w k₀) ^ 2 * (k₀.factorial : ℝ) * (C x) ^ k₀ ≤
        ∑ k ∈ Finset.range (D + 1), (w k) ^ 2 * (k.factorial : ℝ) * (C x) ^ k :=
      Finset.single_le_sum hterm_nonneg hk₀
    have hpowC : (c₁ / ‖x‖ ^ 2) ^ k₀ ≤ (C x) ^ k₀ :=
      pow_le_pow_left₀ (by positivity) hClow k₀
    have hr8 : ‖x‖ ^ (2 * k₀) ≤ ‖x‖ ^ 8 := pow_le_pow_of_le_one hr.le hr1 (by omega)
    have hkey : c₁ ^ k₀ ≤ ‖x‖ ^ 8 * (c₁ / ‖x‖ ^ 2) ^ k₀ := by
      rw [div_pow, ← pow_mul, mul_div_assoc', le_div_iff₀ (by positivity)]
      nlinarith [pow_pos hc₁ k₀]
    calc (w k₀) ^ 2 * (k₀.factorial : ℝ) * c₁ ^ k₀
        ≤ (w k₀) ^ 2 * (k₀.factorial : ℝ) * (‖x‖ ^ 8 * (c₁ / ‖x‖ ^ 2) ^ k₀) := by
          gcongr
      _ = ‖x‖ ^ 8 * ((w k₀) ^ 2 * (k₀.factorial : ℝ) * (c₁ / ‖x‖ ^ 2) ^ k₀) := by ring
      _ ≤ ‖x‖ ^ 8 * ((w k₀) ^ 2 * (k₀.factorial : ℝ) * (C x) ^ k₀) := by gcongr
      _ ≤ ‖x‖ ^ 8 * ∑ k ∈ Finset.range (D + 1), (w k) ^ 2 * (k.factorial : ℝ) * (C x) ^ k := by
          gcongr
  · -- all degrees ≤ 3: upper bound by M |x|²
    push_neg at hbig
    set M : ℝ := ∑ k ∈ Finset.range (D + 1), (w k) ^ 2 * (k.factorial : ℝ) * c₂ ^ k with hM
    refine not_UVTrace_of_upper_bound S z₁ z₂ κ hκ (C := M) two_pos one_pos ?_
    intro x hx hx1
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hr1 : ‖x‖ ≤ 1 := hx1.le
    have hClow := hlow x hx hr1
    have hCup := hup x hx hr1
    have hCnn : 0 ≤ C x := le_trans (by positivity) hClow
    rw [hθ x hx, Real.rpow_two]
    have hnn : 0 ≤ ‖x‖ ^ 8 *
        ∑ k ∈ Finset.range (D + 1), (w k) ^ 2 * (k.factorial : ℝ) * (C x) ^ k := by
      apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg (fun k _ => by positivity)
    rw [abs_of_nonneg hnn, hM, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum (fun k hk => ?_)
    by_cases h4 : 4 ≤ k
    · simp [hbig k hk h4]
    · push_neg at h4
      have hpow : (C x) ^ k ≤ (c₂ / ‖x‖ ^ 2) ^ k := pow_le_pow_left₀ hCnn hCup k
      have hsplit : ‖x‖ ^ 8 = ‖x‖ ^ (2 * k) * ‖x‖ ^ (8 - 2 * k) := by
        rw [← pow_add]; congr 1; omega
      have hr2 : ‖x‖ ^ (8 - 2 * k) ≤ ‖x‖ ^ 2 := pow_le_pow_of_le_one hr.le hr1 (by omega)
      have hfac : 0 ≤ (w k) ^ 2 * (k.factorial : ℝ) := by positivity
      calc ‖x‖ ^ 8 * ((w k) ^ 2 * (k.factorial : ℝ) * (C x) ^ k)
          ≤ ‖x‖ ^ 8 * ((w k) ^ 2 * (k.factorial : ℝ) * (c₂ / ‖x‖ ^ 2) ^ k) := by gcongr
        _ = (w k) ^ 2 * (k.factorial : ℝ) * c₂ ^ k * ‖x‖ ^ (8 - 2 * k) := by
          rw [hsplit, div_pow, ← pow_mul]
          field_simp
        _ ≤ (w k) ^ 2 * (k.factorial : ℝ) * c₂ ^ k * ‖x‖ ^ 2 := by gcongr

end ClayYM
