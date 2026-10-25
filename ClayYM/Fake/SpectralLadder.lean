/-
ClayYM/Fake/SpectralLadder.lean  (v1.1)
=======================================
GUARD (b): the spectral ladder `H Ω = 0`, `H e_n = e_n / n` (`n ≥ 1`), written in correlation form
`⟪v, e^{-tH} w⟫ = Σ_n e^{-t λ_n} v_n w_n` on finitely supported coefficient vectors (`λ_0 = 0`).

Proved (no `sorry`, no axiom):
* `trunc_qGap`, `trunc_massGap` : every truncation (modes `≤ N`, `N ≥ 1`) has a gap, in both forms:
  q-form with `q_N = e^{-ℓ/N}`, and mass gap `Δ_N = 1/N`;
* `not_qGap`, `not_massGap`      : the union of the truncations (all finitely supported vectors) has
  NO gap, in either form (`q_N → 1`, `Δ_N → 0`);
* `truncation_inference_fails`   : the inference "every truncation has a q-gap ⟹ the union has one"
  is FALSE;
* `approx_qGap`, `approx_converges`, `closure_needs_same_q` : the same failure for a sequence of
  approximating theories converging pointwise (energies `1/n` below `N`, `1` above): the closure
  lemma `Transfer.QGapOn.of_tendsto` cannot be weakened to "each approximant has its own `q`".

This model is a test of quantifiers, not a quantum field theory: it does not satisfy (and does not
claim) any Yang–Mills clause.
-/
import ClayYM.Transfer

open Filter Topology

noncomputable section

namespace ClayYM.Ladder

open Transfer

/-- Energies `λ_n = 1/n` (`λ_0 = 0`: the vacuum). -/
def lam (n : ℕ) : ℝ := (n : ℝ)⁻¹

/-- Operations on finitely supported coefficient vectors; the vacuum is `e_0`. -/
def ops : VecOps (ℕ →₀ ℝ) := ⟨(· + ·), (· • ·), Finsupp.single 0 1⟩

/-- Correlations of the diagonal model with energies `μ`:
`⟪v, e^{-tH} w⟫ = Σ_n e^{-t μ_n} v_n w_n`. -/
def Bμ (μ : ℕ → ℝ) (v w : ℕ →₀ ℝ) (t : ℝ) : ℝ :=
  v.sum fun n a => Real.exp (-(t * μ n)) * a * w n

/-- The ladder `H e_n = e_n / n`. -/
abbrev ladder : (ℕ →₀ ℝ) → (ℕ →₀ ℝ) → ℝ → ℝ := Bμ lam

/-- Truncation `N`: vectors supported on the modes `0, …, N`. -/
def D (N : ℕ) : Set (ℕ →₀ ℝ) := {v | ∀ n, N < n → v n = 0}

lemma lam_zero : lam 0 = 0 := by simp [lam]

theorem isBilin (μ : ℕ → ℝ) : IsBilin ops (Bμ μ) where
  add_left F F' G t := by
    simp only [ops, Bμ]
    apply Finsupp.sum_add_index'
    · intro n; simp
    · intro n a b; ring
  add_right F G G' t := by
    simp only [ops, Bμ, Finsupp.coe_add, Pi.add_apply, mul_add]
    exact Finsupp.sum_add
  smul_left c F G t := by
    simp only [ops, Bμ]
    rw [Finsupp.sum_smul_index' (by intro n; simp), Finsupp.mul_sum]
    apply Finsupp.sum_congr
    intro n _
    simp only [smul_eq_mul]
    ring
  smul_right c F G t := by
    simp only [ops, Bμ, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [Finsupp.mul_sum]
    apply Finsupp.sum_congr
    intro n _
    ring

lemma Bμ_vac_left (μ : ℕ → ℝ) (hμ : μ 0 = 0) (w : ℕ →₀ ℝ) (t : ℝ) :
    Bμ μ ops.Ω w t = w 0 := by
  simp only [ops, Bμ]
  rw [Finsupp.sum_single_index (by simp)]
  simp [hμ]

lemma Bμ_vac_right (μ : ℕ → ℝ) (hμ : μ 0 = 0) (v : ℕ →₀ ℝ) (t : ℝ) :
    Bμ μ v ops.Ω t = v 0 := by
  simp only [ops, Bμ, Finsupp.sum]
  rw [Finset.sum_eq_single 0]
  · simp [hμ]
  · intro n _ hn
    simp [Finsupp.single_apply, Ne.symm hn]
  · intro h0
    simp [Finsupp.notMem_support_iff.1 h0]

lemma Bμ_self (μ : ℕ → ℝ) (v : ℕ →₀ ℝ) (t : ℝ) :
    Bμ μ v v t = ∑ n ∈ v.support, Real.exp (-(t * μ n)) * v n ^ 2 := by
  simp only [Bμ, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Truncated correlation of the diagonal model: the vacuum mode is removed. -/
lemma Bμ_trunc_self (μ : ℕ → ℝ) (hμ : μ 0 = 0) (v : ℕ →₀ ℝ) (t : ℝ) :
    Bμ μ (ops.trunc (Bμ μ) v) (ops.trunc (Bμ μ) v) t =
      ∑ n ∈ v.support.erase 0, Real.exp (-(t * μ n)) * v n ^ 2 := by
  rw [(isBilin μ).trunc_trunc]
  simp only [truncCorr, Bμ_vac_left μ hμ, Bμ_vac_right μ hμ, Bμ_self]
  have hΩ0 : (ops.Ω : ℕ →₀ ℝ) 0 = 1 := by simp [ops]
  rw [hΩ0]
  by_cases h0 : 0 ∈ v.support
  · rw [← Finset.add_sum_erase _ _ h0]
    simp [hμ]
    ring
  · rw [Finset.erase_eq_of_notMem h0, Finsupp.notMem_support_iff.1 h0]
    ring

lemma Bμ_corr (μ : ℕ → ℝ) (hμ : μ 0 = 0) (F G : ℕ →₀ ℝ) (t : ℝ) :
    Bμ μ F G t - Bμ μ F ops.Ω 0 * Bμ μ ops.Ω G 0 =
      ∑ n ∈ F.support.erase 0, Real.exp (-(t * μ n)) * F n * G n := by
  rw [Bμ_vac_right μ hμ, Bμ_vac_left μ hμ]
  simp only [Bμ, Finsupp.sum]
  by_cases h0 : 0 ∈ F.support
  · rw [← Finset.add_sum_erase _ _ h0]
    simp [hμ]
  · rw [Finset.erase_eq_of_notMem h0, Finsupp.notMem_support_iff.1 h0]
    ring

/-- A uniform lower bound `m` on the energies seen by `𝒜` gives the q-form with `q = e^{-ℓ m}`. -/
lemma qGap_of_lower (μ : ℕ → ℝ) (hμ : μ 0 = 0) (𝒜 : Set (ℕ →₀ ℝ)) {m ℓ : ℝ} (hm : 0 < m)
    (hℓ : 0 < ℓ) (hlow : ∀ v ∈ 𝒜, ∀ n ∈ v.support, n ≠ 0 → m ≤ μ n) :
    QGapOn ops (Bμ μ) 𝒜 ℓ (Real.exp (-(ℓ * m))) := by
  refine ⟨hℓ, Real.exp_pos _, Real.exp_lt_one_iff.2 (neg_neg_of_pos (mul_pos hℓ hm)),
    fun A hA => ?_⟩
  rw [Bμ_trunc_self μ hμ A ℓ, Bμ_trunc_self μ hμ A 0, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hle : m ≤ μ n := hlow A hA n (Finset.mem_of_mem_erase hn) (Finset.ne_of_mem_erase hn)
  have hexp : Real.exp (-(ℓ * μ n)) ≤ Real.exp (-(ℓ * m)) := by
    apply Real.exp_le_exp.2
    nlinarith
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul]
  exact mul_le_mul_of_nonneg_right hexp (sq_nonneg _)

/-- **Every truncation has a gap (q-form).** -/
theorem trunc_qGap (N : ℕ) (hN : 1 ≤ N) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    QGapOn ops ladder (D N) ℓ (Real.exp (-(ℓ * (N : ℝ)⁻¹))) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine qGap_of_lower lam lam_zero (D N) (inv_pos.2 hN') hℓ fun v hv n hn hn0 => ?_
  have hnN : n ≤ N := by
    by_contra h
    push Not at h
    exact (Finsupp.mem_support_iff.1 hn) (hv n h)
  have hn1 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  exact inv_anti₀ hn1 (by exact_mod_cast hnN)

lemma ladder_single_trunc (n : ℕ) (hn : n ≠ 0) (t : ℝ) :
    ladder (ops.trunc ladder (Finsupp.single n 1)) (ops.trunc ladder (Finsupp.single n 1)) t =
      Real.exp (-(t * lam n)) := by
  show Bμ lam (ops.trunc (Bμ lam) _) (ops.trunc (Bμ lam) _) t = _
  rw [Bμ_trunc_self lam lam_zero]
  have hs : (Finsupp.single n (1 : ℝ)).support.erase 0 = {n} := by
    rw [Finsupp.support_single_ne_zero n one_ne_zero]
    exact Finset.erase_eq_of_notMem (by simpa using Ne.symm hn)
  rw [hs]
  simp

/-- **The union of the truncations has no q-gap.** -/
theorem not_qGap (ℓ q : ℝ) : ¬ QGapOn ops ladder Set.univ ℓ q := by
  rintro ⟨_, _, hq1, h⟩
  have hle : ∀ n : ℕ, 1 ≤ n → Real.exp (-(ℓ * lam n)) ≤ q := by
    intro n hn
    have hn0 : n ≠ 0 := by omega
    have := h (Finsupp.single n 1) (Set.mem_univ _)
    rw [ladder_single_trunc n hn0, ladder_single_trunc n hn0] at this
    simpa using this
  have hlim : Tendsto (fun n : ℕ => Real.exp (-(ℓ * lam n))) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => lam n) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => -(ℓ * lam n)) atTop (𝓝 (-(ℓ * 0))) := (h1.const_mul ℓ).neg
    rw [mul_zero, neg_zero] at h2
    have h3 := (Real.continuous_exp.tendsto 0).comp h2
    rw [Real.exp_zero] at h3
    exact h3
  have : (1 : ℝ) ≤ q := le_of_tendsto hlim (eventually_atTop.2 ⟨1, hle⟩)
  linarith

lemma D_mono : Monotone D := fun _ _ hNM _ hv n hn => hv n (lt_of_le_of_lt hNM hn)

lemma iUnion_D : (⋃ N, D N) = Set.univ := by
  ext v
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  refine ⟨v.support.sup id, fun n hn => ?_⟩
  by_contra h
  have hmem : n ∈ v.support := Finsupp.mem_support_iff.2 h
  have := Finset.le_sup (f := id) hmem
  simp only [id] at this
  omega

/-- **Guard (b).** "Every truncation has a q-gap ⟹ the union of the truncations has one" is false. -/
theorem truncation_inference_fails :
    ¬ ∀ (V : Type) (o : VecOps V) (B : V → V → ℝ → ℝ) (D : ℕ → Set V) (ℓ : ℝ), 0 < ℓ →
      Monotone D → (∀ N, ∃ q, QGapOn o B (D N) ℓ q) → ∃ q, QGapOn o B (⋃ N, D N) ℓ q := by
  intro h
  obtain ⟨q, hq⟩ := h (ℕ →₀ ℝ) ops ladder D 1 one_pos D_mono fun N =>
    ⟨_, (trunc_qGap (max N 1) (le_max_right _ _) one_pos).mono (D_mono (le_max_left _ _))⟩
  rw [iUnion_D] at hq
  exact not_qGap 1 q hq

/-! ### The same guard for the mass-gap form of `ClayYM.HasMassGap` -/

/-- **Every truncation has a mass gap** `Δ_N = 1/N` (form of `ClayYM.HasMassGap`). -/
theorem trunc_massGap (N : ℕ) (hN : 1 ≤ N) : MassGapOn ops ladder (D N) (1 / N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨by positivity, fun F hF G _ t ht => ?_⟩
  rw [Bμ_corr lam lam_zero F G t]
  have hw : ∀ n ∈ F.support.erase 0, Real.exp (-(t * lam n)) ≤ Real.exp (-(1 / N * t)) := by
    intro n hn
    have hn0 := Finset.ne_of_mem_erase hn
    have hnN : n ≤ N := by
      by_contra h
      push Not at h
      exact (Finsupp.mem_support_iff.1 (Finset.mem_of_mem_erase hn)) (hF n h)
    have hn1 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hlam : (1 : ℝ) / N ≤ lam n := by
      rw [one_div]
      exact inv_anti₀ hn1 (by exact_mod_cast hnN)
    apply Real.exp_le_exp.2
    nlinarith
  have hFF : ladder F F 0 = ∑ n ∈ F.support, F n ^ 2 := by
    rw [show ladder F F 0 = Bμ lam F F 0 from rfl, Bμ_self]; simp
  have hGG : ladder G G 0 = ∑ n ∈ G.support, G n ^ 2 := by
    rw [show ladder G G 0 = Bμ lam G G 0 from rfl, Bμ_self]; simp
  set s := F.support.erase 0 with hs_def
  have hsF : ∑ n ∈ s, F n ^ 2 ≤ ∑ n ∈ F.support, F n ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun _ _ _ => sq_nonneg _
  have hsG : ∑ n ∈ s, G n ^ 2 ≤ ∑ n ∈ G.support, G n ^ 2 := by
    calc ∑ n ∈ s, G n ^ 2 = ∑ n ∈ s ∩ G.support, G n ^ 2 := by
          refine (Finset.sum_subset Finset.inter_subset_left fun n _ hn => ?_).symm
          have : G n = 0 := by
            by_contra h
            exact hn (Finset.mem_inter.2 ⟨‹n ∈ s›, Finsupp.mem_support_iff.2 h⟩)
          simp [this]
      _ ≤ ∑ n ∈ G.support, G n ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun _ _ _ => sq_nonneg _
  have hc : 0 ≤ Real.exp (-(1 / N * t)) := (Real.exp_pos _).le
  calc |∑ n ∈ s, Real.exp (-(t * lam n)) * F n * G n|
      ≤ ∑ n ∈ s, |Real.exp (-(t * lam n)) * F n * G n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ s, Real.exp (-(1 / N * t)) * (|F n| * |G n|) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), mul_assoc]
        exact mul_le_mul_of_nonneg_right (hw n hn) (by positivity)
    _ = Real.exp (-(1 / N * t)) * ∑ n ∈ s, |F n| * |G n| := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-(1 / N * t)) * (√(∑ n ∈ s, |F n| ^ 2) * √(∑ n ∈ s, |G n| ^ 2)) :=
        mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) hc
    _ = Real.exp (-(1 / N * t)) * (√(∑ n ∈ s, F n ^ 2) * √(∑ n ∈ s, G n ^ 2)) := by
        simp only [sq_abs]
    _ ≤ Real.exp (-(1 / N * t)) * (√(ladder F F 0) * √(ladder G G 0)) := by
        rw [hFF, hGG]
        gcongr
    _ = Real.exp (-(1 / N * t)) * √(ladder F F 0) * √(ladder G G 0) := by ring

/-- **The union has no mass gap** (form of `ClayYM.HasMassGap`). -/
theorem not_massGap (Δ : ℝ) : ¬ MassGapOn ops ladder Set.univ Δ := by
  rintro ⟨hΔ, h⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / Δ)
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
    linarith [one_div_pos.2 hΔ]
  have h1 := h (Finsupp.single n 1) (Set.mem_univ _) (Finsupp.single n 1) (Set.mem_univ _) 1
    zero_le_one
  rw [Bμ_corr lam lam_zero] at h1
  have hs : (Finsupp.single n (1 : ℝ)).support.erase 0 = {n} := by
    rw [Finsupp.support_single_ne_zero n one_ne_zero]
    exact Finset.erase_eq_of_notMem (by simpa using Ne.symm hn0)
  have hself : ladder (Finsupp.single n 1) (Finsupp.single n 1) 0 = 1 := by
    rw [show ladder (Finsupp.single n 1) (Finsupp.single n 1) 0 =
      Bμ lam (Finsupp.single n 1) (Finsupp.single n 1) 0 from rfl, Bμ_self,
      Finsupp.support_single_ne_zero n one_ne_zero]
    simp
  rw [hs, hself] at h1
  simp only [Finset.sum_singleton, Finsupp.single_eq_same, mul_one, one_mul, Real.sqrt_one,
    abs_of_pos (Real.exp_pos _)] at h1
  have h2 := Real.exp_le_exp.1 h1
  have hn1 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have : Δ ≤ lam n := by linarith
  rw [lam] at this
  have h3 : 1 / Δ < n := hn
  rw [div_lt_iff₀ hΔ] at h3
  have h4 : Δ * n ≤ 1 := by
    calc Δ * n ≤ (n : ℝ)⁻¹ * n := mul_le_mul_of_nonneg_right this hn1.le
      _ = 1 := inv_mul_cancel₀ hn1.ne'
  linarith

/-! ### Approximating theories: the closure lemma needs the SAME `q` -/

/-- Approximant `N`: energies `1/n` for `n ≤ N`, energy `1` above. -/
def lamN (N n : ℕ) : ℝ := if n ≤ N then lam n else 1

/-- Every approximant has a q-gap, `q_N = e^{-ℓ / max N 1}`. -/
theorem approx_qGap (N : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    QGapOn ops (Bμ (lamN N)) Set.univ ℓ (Real.exp (-(ℓ * ((max N 1 : ℕ) : ℝ)⁻¹))) := by
  have hM : (0 : ℝ) < ((max N 1 : ℕ) : ℝ) := by exact_mod_cast lt_of_lt_of_le one_pos (le_max_right N 1)
  refine qGap_of_lower (lamN N) (by simp [lamN, lam]) Set.univ (inv_pos.2 hM) hℓ
    fun v _ n _ hn0 => ?_
  have hn1 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  unfold lamN
  split_ifs with hnN
  · exact inv_anti₀ hn1 (by exact_mod_cast hnN.trans (le_max_left N 1))
  · exact inv_le_one_of_one_le₀ (by exact_mod_cast le_max_right N 1)

lemma approx_eq (F G : ℕ →₀ ℝ) (t : ℝ) (N : ℕ) (hN : F.support.sup id ≤ N) :
    Bμ (lamN N) F G t = ladder F G t := by
  simp only [Bμ, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro n hn
  have : n ≤ N := (Finset.le_sup (f := id) hn).trans hN
  simp [lamN, this]

/-- The approximants converge pointwise to the ladder (eventually equal on each pair). -/
theorem approx_converges (ℓ : ℝ) :
    ConvergesOn atTop ops (fun N => Bμ (lamN N)) ladder Set.univ ℓ := by
  intro F _ G _ t _
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (F.support.sup id)] with N hN
  exact (approx_eq F G t N hN).symm

/-- **Guard for the closure lemma.** Pointwise convergence + a q-gap for each approximant (with its
own `q`) does NOT give a q-gap for the limit: the SAME `q` is necessary. -/
theorem closure_needs_same_q :
    ¬ ∀ (V : Type) (o : VecOps V) (Bk : ℕ → V → V → ℝ → ℝ) (B : V → V → ℝ → ℝ) (ℓ : ℝ), 0 < ℓ →
      (∀ k, IsBilin o (Bk k)) → IsBilin o B → ConvergesOn atTop o Bk B Set.univ ℓ →
      (∀ k, ∃ q, QGapOn o (Bk k) Set.univ ℓ q) → ∃ q, QGapOn o B Set.univ ℓ q := by
  intro h
  obtain ⟨q, hq⟩ := h (ℕ →₀ ℝ) ops (fun N => Bμ (lamN N)) ladder 1 one_pos
    (fun N => isBilin _) (isBilin _) (approx_converges 1) fun N => ⟨_, approx_qGap N one_pos⟩
  exact not_qGap 1 q hq

end ClayYM.Ladder
