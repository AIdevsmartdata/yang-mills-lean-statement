/-
ClayYM/Transfer.lean  (v1.1)
============================
Abstract layer of the mass gap: the gap as a uniform bound on the transfer form, its closure under
limits, and its relation with the operator form `‖e^{-tH}(1 − P_Ω)‖ ≤ e^{-Δt}`.

No axiom, no `sorry`. The Osterwalder–Schrader reconstruction is NOT proved here: it enters only as
the NAMED HYPOTHESIS `Recon` (a structure passed as an explicit argument, never asserted).

* `VecOps`, `IsBilin` : formal operations on the vectors of the OS pre-Hilbert space (for families of
  test functions: concatenation, scaling, vacuum) and bilinearity of the OS form
  `B F G t = ⟪F, τ_t G⟫` for these operations;
* `MassGapOn`         : the mass gap of `ClayYM.HasMassGap`, restricted to a set of vectors;
* `QGapOn`            : the q-form `0 < q < 1 ∧ ∀ A ∈ 𝒜₀, ⟨v_A, e^{-ℓH} v_A⟩ ≤ q ‖v_A‖²`, with the
                        truncated vector `v_A = A − ⟨Ω, A⟩ Ω`;
* `QGapOn.of_tendsto` : CLOSURE LEMMA (pointwise limits, along any filter, with the SAME `q`);
* `decay_of_qbound`   : elementary semigroup estimate (bound at one time `ℓ` ⟹ bound `q^{t/ℓ}` at every
                        time `t ≥ 0`; no spectral theorem);
* `Recon`             : reconstruction data (real Hilbert space, class map, strongly continuous
                        transfer semigroup of self-adjoint contractions);
* `Recon.massGapOn_of_qGapOn`     : q-form + density ⟹ mass gap `Δ = −log q / ℓ`;
* `MassGapOn.qGapOn`              : mass gap `Δ` ⟹ q-form with `q = e^{−Δℓ}` (no reconstruction);
* `Recon.vacuum_unique`           : q-form + density ⟹ every vector fixed by `e^{-ℓH}` is a multiple
                                    of `Ω` (uniqueness of the vacuum is a CONSEQUENCE, not a hypothesis);
* `Recon.massGapOn_univ_iff_opNorm` : mass gap ⟺ `‖e^{-tH}(1 − P_Ω)‖ ≤ e^{-Δt}` for all `t ≥ 0`.
-/
import Mathlib

open Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace ClayYM.Transfer

universe u

variable {V : Type u}

/-! ### Formal operations and the two forms of the gap -/

/-- Formal operations on the vectors of the OS pre-Hilbert space: formal sum, scaling, vacuum.
No law is assumed; the laws used are stated separately (`IsBilin`). -/
structure VecOps (V : Type u) where
  add : V → V → V
  smul : ℝ → V → V
  Ω : V

/-- Bilinearity of the OS form `B F G t = ⟪F, τ_t G⟫` for the formal operations. -/
structure IsBilin (o : VecOps V) (B : V → V → ℝ → ℝ) : Prop where
  add_left : ∀ F F' G t, B (o.add F F') G t = B F G t + B F' G t
  add_right : ∀ F G G' t, B F (o.add G G') t = B F G t + B F G' t
  smul_left : ∀ c F G t, B (o.smul c F) G t = c * B F G t
  smul_right : ∀ c F G t, B F (o.smul c G) t = c * B F G t

/-- Truncated vector `v_A = A − ⟨Ω, A⟩ Ω`, with `⟨Ω, A⟩ = B Ω A 0`. -/
def VecOps.trunc (o : VecOps V) (B : V → V → ℝ → ℝ) (A : V) : V :=
  o.add A (o.smul (-(B o.Ω A 0)) o.Ω)

/-- Mass gap `Δ` restricted to a set `D` of vectors. With `D = univ` and the OS form of a Schwinger
function this is exactly `ClayYM.HasMassGap` (see `ClayYM.hasMassGap_iff_massGapOn`). -/
def MassGapOn (o : VecOps V) (B : V → V → ℝ → ℝ) (D : Set V) (Δ : ℝ) : Prop :=
  0 < Δ ∧ ∀ F ∈ D, ∀ G ∈ D, ∀ t : ℝ, 0 ≤ t →
    |B F G t - B F o.Ω 0 * B o.Ω G 0| ≤
      Real.exp (-(Δ * t)) * Real.sqrt (B F F 0) * Real.sqrt (B G G 0)

/-- **q-form of the gap** on a set `𝒜₀`, at the physical time `ℓ`:
`0 < q < 1` and `⟨v_A, e^{-ℓH} v_A⟩ ≤ q ‖v_A‖²` for every `A ∈ 𝒜₀`. The SAME `q` serves every `A`
(the statement `∃ q, QGapOn o B 𝒜₀ ℓ q` is `∃ q < 1, ∀ A ∈ 𝒜₀, …`). -/
def QGapOn (o : VecOps V) (B : V → V → ℝ → ℝ) (𝒜₀ : Set V) (ℓ q : ℝ) : Prop :=
  0 < ℓ ∧ 0 < q ∧ q < 1 ∧
    ∀ A ∈ 𝒜₀, B (o.trunc B A) (o.trunc B A) ℓ ≤ q * B (o.trunc B A) (o.trunc B A) 0

lemma QGapOn.mono {o : VecOps V} {B : V → V → ℝ → ℝ} {𝒜₀ 𝒜₁ : Set V} {ℓ q : ℝ}
    (h : QGapOn o B 𝒜₁ ℓ q) (hsub : 𝒜₀ ⊆ 𝒜₁) : QGapOn o B 𝒜₀ ℓ q :=
  ⟨h.1, h.2.1, h.2.2.1, fun A hA => h.2.2.2 A (hsub hA)⟩

lemma MassGapOn.mono {o : VecOps V} {B : V → V → ℝ → ℝ} {D D' : Set V} {Δ : ℝ}
    (h : MassGapOn o B D' Δ) (hsub : D ⊆ D') : MassGapOn o B D Δ :=
  ⟨h.1, fun F hF G hG t ht => h.2 F (hsub hF) G (hsub hG) t ht⟩

/-- Expanded truncated correlation (a polynomial in finitely many values of `B`). -/
def truncCorr (o : VecOps V) (B : V → V → ℝ → ℝ) (A : V) (t : ℝ) : ℝ :=
  B A A t - B o.Ω A 0 * B A o.Ω t - B o.Ω A 0 * B o.Ω A t + B o.Ω A 0 ^ 2 * B o.Ω o.Ω t

lemma IsBilin.trunc_trunc {o : VecOps V} {B : V → V → ℝ → ℝ} (h : IsBilin o B) (A : V) (t : ℝ) :
    B (o.trunc B A) (o.trunc B A) t = truncCorr o B A t := by
  simp only [VecOps.trunc, truncCorr, h.add_left, h.add_right, h.smul_left, h.smul_right]
  ring

lemma IsBilin.vac_trunc {o : VecOps V} {B : V → V → ℝ → ℝ} (h : IsBilin o B)
    (hΩ : B o.Ω o.Ω 0 = 1) (A : V) : B o.Ω (o.trunc B A) 0 = 0 := by
  simp only [VecOps.trunc, h.add_right, h.smul_right, hΩ]
  ring

/-! ### Closure lemma -/

/-- Pointwise convergence of the transfer form on `𝒜₀ ∪ {Ω}`, at the two times `0` and `ℓ`
(the weakest convergence used by the closure lemma). -/
def ConvergesOn {α : Type*} (L : Filter α) (o : VecOps V) (Bk : α → V → V → ℝ → ℝ)
    (B : V → V → ℝ → ℝ) (𝒜₀ : Set V) (ℓ : ℝ) : Prop :=
  ∀ F ∈ insert o.Ω 𝒜₀, ∀ G ∈ insert o.Ω 𝒜₀, ∀ t ∈ ({0, ℓ} : Set ℝ),
    Tendsto (fun k => Bk k F G t) L (𝓝 (B F G t))

/-- **Closure lemma.** If the forms `Bk k` converge pointwise on `𝒜₀ ∪ {Ω}` (times `0` and `ℓ`) and
eventually satisfy the q-form with the SAME `q`, the limit satisfies it. Any filter: sequences,
subsequences, nets (no choice of subsequence is needed). -/
theorem QGapOn.of_tendsto {α : Type*} {L : Filter α} [L.NeBot] {o : VecOps V}
    {Bk : α → V → V → ℝ → ℝ} {B : V → V → ℝ → ℝ} {𝒜₀ : Set V} {ℓ q : ℝ}
    (hbk : ∀ k, IsBilin o (Bk k)) (hb : IsBilin o B) (hconv : ConvergesOn L o Bk B 𝒜₀ ℓ)
    (h : ∀ᶠ k in L, QGapOn o (Bk k) 𝒜₀ ℓ q) : QGapOn o B 𝒜₀ ℓ q := by
  obtain ⟨k₀, hk₀⟩ := h.exists
  refine ⟨hk₀.1, hk₀.2.1, hk₀.2.2.1, fun A hA => ?_⟩
  have hA' : A ∈ insert o.Ω 𝒜₀ := Set.mem_insert_of_mem _ hA
  have hΩ' : o.Ω ∈ insert o.Ω 𝒜₀ := Set.mem_insert _ _
  have h0 : (0 : ℝ) ∈ ({0, ℓ} : Set ℝ) := by simp
  have hℓ : ℓ ∈ ({0, ℓ} : Set ℝ) := by simp
  have tc : ∀ t ∈ ({0, ℓ} : Set ℝ),
      Tendsto (fun k => truncCorr o (Bk k) A t) L (𝓝 (truncCorr o B A t)) := by
    intro t ht
    unfold truncCorr
    have e1 := hconv A hA' A hA' t ht
    have e2 := hconv o.Ω hΩ' A hA' 0 h0
    have e3 := hconv A hA' o.Ω hΩ' t ht
    have e4 := hconv o.Ω hΩ' A hA' t ht
    have e5 := hconv o.Ω hΩ' o.Ω hΩ' t ht
    exact ((e1.sub (e2.mul e3)).sub (e2.mul e4)).add ((e2.pow 2).mul e5)
  rw [hb.trunc_trunc, hb.trunc_trunc]
  have hev : ∀ᶠ k in L, truncCorr o (Bk k) A ℓ ≤ q * truncCorr o (Bk k) A 0 := by
    filter_upwards [h] with k hk
    rw [← (hbk k).trunc_trunc, ← (hbk k).trunc_trunc]
    exact hk.2.2.2 A hA
  exact le_of_tendsto_of_tendsto (tc ℓ hℓ) ((tc 0 h0).const_mul q) hev

/-! ### From the gap to the q-form (no reconstruction needed) -/

/-- Mass gap `Δ` ⟹ q-form with `q = e^{−Δℓ}`, for any `𝒜₀` and any `ℓ > 0`. Uses only bilinearity,
the normalisation `⟨Ω, Ω⟩ = 1` and reflection positivity `0 ≤ ⟨F, F⟩`. -/
theorem MassGapOn.qGapOn {o : VecOps V} {B : V → V → ℝ → ℝ} {Δ ℓ : ℝ} (hb : IsBilin o B)
    (hΩ : B o.Ω o.Ω 0 = 1) (hpos : ∀ F, 0 ≤ B F F 0) (h : MassGapOn o B Set.univ Δ)
    (hℓ : 0 < ℓ) (𝒜₀ : Set V) : QGapOn o B 𝒜₀ ℓ (Real.exp (-(Δ * ℓ))) := by
  refine ⟨hℓ, Real.exp_pos _, Real.exp_lt_one_iff.2 (neg_neg_of_pos (mul_pos h.1 hℓ)), fun A _ => ?_⟩
  have h0 : B o.Ω (o.trunc B A) 0 = 0 := hb.vac_trunc hΩ A
  have h1 := h.2 (o.trunc B A) (Set.mem_univ _) (o.trunc B A) (Set.mem_univ _) ℓ hℓ.le
  rw [h0, mul_zero, sub_zero, mul_assoc, Real.mul_self_sqrt (hpos _)] at h1
  exact (le_abs_self _).trans h1

/-! ### Elementary semigroup estimate -/

section Decay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Semigroup estimate.** Let `T` be a semigroup of self-adjoint contractions fixing `ω`. If
`⟨w, T ℓ w⟩ ≤ q ‖w‖²` for every `w ⊥ ω`, then `‖T t w‖ ≤ q^{t/ℓ} ‖w‖` for every `t ≥ 0` and `w ⊥ ω`.
Proof: halving (`‖T(s/2) w‖² = ⟨w, T s w⟩`), dyadic times, then a limit. No spectral theorem. -/
theorem decay_of_qbound (T : ℝ → E →L[ℝ] E) (ω : E) {ℓ q : ℝ}
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t))
    (hsymm : ∀ t, 0 ≤ t → ∀ x y, ⟪T t x, y⟫ = ⟪x, T t y⟫)
    (hcontr : ∀ t, 0 ≤ t → ‖T t‖ ≤ 1)
    (hvac : ∀ t, 0 ≤ t → T t ω = ω)
    (hℓ : 0 < ℓ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hb : ∀ w, ⟪ω, w⟫ = 0 → ⟪w, T ℓ w⟫ ≤ q * ‖w‖ ^ 2) :
    ∀ t, 0 ≤ t → ∀ w, ⟪ω, w⟫ = 0 → ‖T t w‖ ≤ q ^ (t / ℓ) * ‖w‖ := by
  have hinv : ∀ t, 0 ≤ t → ∀ w, ⟪ω, w⟫ = 0 → ⟪ω, T t w⟫ = 0 := by
    intro t ht w hw
    rw [← hsymm t ht, hvac t ht, hw]
  have hc : ∀ t, 0 ≤ t → ∀ w, ‖T t w‖ ≤ ‖w‖ := by
    intro t ht w
    calc ‖T t w‖ ≤ ‖T t‖ * ‖w‖ := (T t).le_opNorm w
      _ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right (hcontr t ht) (norm_nonneg w)
      _ = ‖w‖ := one_mul _
  have hsq : ∀ s, 0 ≤ s → ∀ w, ‖T (s / 2) w‖ ^ 2 = ⟪w, T s w⟫ := by
    intro s hs w
    have hs2 : 0 ≤ s / 2 := by linarith
    rw [← real_inner_self_eq_norm_sq, hsymm (s / 2) hs2, ← ContinuousLinearMap.comp_apply,
      ← hadd _ _ hs2 hs2, add_halves]
  have hhalf : ∀ s, 0 ≤ s → ∀ c, 0 ≤ c →
      (∀ w, ⟪ω, w⟫ = 0 → ‖T s w‖ ≤ c * ‖w‖) →
      ∀ w, ⟪ω, w⟫ = 0 → ‖T (s / 2) w‖ ≤ Real.sqrt c * ‖w‖ := by
    intro s hs c hc0 hcs w hw
    have h1 : ‖T (s / 2) w‖ ^ 2 ≤ (Real.sqrt c * ‖w‖) ^ 2 := by
      rw [hsq s hs w, mul_pow, Real.sq_sqrt hc0]
      calc ⟪w, T s w⟫ ≤ ‖w‖ * ‖T s w‖ := real_inner_le_norm _ _
        _ ≤ ‖w‖ * (c * ‖w‖) := mul_le_mul_of_nonneg_left (hcs w hw) (norm_nonneg w)
        _ = c * ‖w‖ ^ 2 := by ring
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 h1
  have hℓ2 : 0 ≤ ℓ / 2 := by linarith
  have hbase : ∀ w, ⟪ω, w⟫ = 0 → ‖T (ℓ / 2) w‖ ≤ Real.sqrt q * ‖w‖ := by
    intro w hw
    have h1 : ‖T (ℓ / 2) w‖ ^ 2 ≤ (Real.sqrt q * ‖w‖) ^ 2 := by
      rw [hsq ℓ hℓ.le w, mul_pow, Real.sq_sqrt hq.le]
      exact hb w hw
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 h1
  have hP0 : ∀ w, ⟪ω, w⟫ = 0 → ‖T ℓ w‖ ≤ q * ‖w‖ := by
    intro w hw
    have e : T ℓ w = T (ℓ / 2) (T (ℓ / 2) w) := by
      rw [← ContinuousLinearMap.comp_apply, ← hadd _ _ hℓ2 hℓ2, add_halves]
    rw [e]
    calc ‖T (ℓ / 2) (T (ℓ / 2) w)‖ ≤ Real.sqrt q * ‖T (ℓ / 2) w‖ :=
          hbase _ (hinv _ hℓ2 w hw)
      _ ≤ Real.sqrt q * (Real.sqrt q * ‖w‖) :=
          mul_le_mul_of_nonneg_left (hbase w hw) (Real.sqrt_nonneg q)
      _ = q * ‖w‖ := by rw [← mul_assoc, Real.mul_self_sqrt hq.le]
  have hdy : ∀ m : ℕ, ∀ w, ⟪ω, w⟫ = 0 →
      ‖T (ℓ / 2 ^ m) w‖ ≤ q ^ ((1 / 2 : ℝ) ^ m) * ‖w‖ := by
    intro m
    induction m with
    | zero => simpa using hP0
    | succ m ih =>
      intro w hw
      have hs : 0 ≤ ℓ / 2 ^ m := by positivity
      have h := hhalf (ℓ / 2 ^ m) hs (q ^ ((1 / 2 : ℝ) ^ m)) (by positivity) ih w hw
      have e1 : ℓ / 2 ^ m / 2 = ℓ / 2 ^ (m + 1) := by rw [pow_succ, div_div]
      have e2 : Real.sqrt (q ^ ((1 / 2 : ℝ) ^ m)) = q ^ ((1 / 2 : ℝ) ^ (m + 1)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hq.le, pow_succ]
      rw [e1, e2] at h
      exact h
  have hmul : ∀ s, 0 ≤ s → ∀ c, 0 ≤ c → (∀ w, ⟪ω, w⟫ = 0 → ‖T s w‖ ≤ c * ‖w‖) →
      ∀ k : ℕ, ∀ w, ⟪ω, w⟫ = 0 → ‖T (k * s) w‖ ≤ c ^ k * ‖w‖ := by
    intro s hs c hc0 hcs k
    induction k with
    | zero => intro w _; simpa using hc 0 le_rfl w
    | succ k ih =>
      intro w hw
      have hks : 0 ≤ (k : ℝ) * s := by positivity
      have e : T (((k + 1 : ℕ) : ℝ) * s) w = T s (T (k * s) w) := by
        rw [← ContinuousLinearMap.comp_apply, ← hadd _ _ hs hks]
        congr 2
        push_cast
        ring
      rw [e]
      calc ‖T s (T (k * s) w)‖ ≤ c * ‖T (k * s) w‖ := hcs _ (hinv _ hks w hw)
        _ ≤ c * (c ^ k * ‖w‖) := mul_le_mul_of_nonneg_left (ih w hw) hc0
        _ = c ^ (k + 1) * ‖w‖ := by ring
  intro t ht w hw
  have hbound : ∀ m : ℕ, ‖T t w‖ ≤ q ^ (t / ℓ - (1 / 2 : ℝ) ^ m) * ‖w‖ := by
    intro m
    have hs : 0 < ℓ / 2 ^ m := by positivity
    have hfl := Nat.floor_le (div_nonneg ht hs.le)
    have hlt := Nat.lt_floor_add_one (t / (ℓ / 2 ^ m))
    set s : ℝ := ℓ / 2 ^ m with hs_def
    set k : ℕ := ⌊t / s⌋₊ with hk_def
    have hks : (k : ℝ) * s ≤ t := by
      calc (k : ℝ) * s ≤ t / s * s := mul_le_mul_of_nonneg_right hfl hs.le
        _ = t := div_mul_cancel₀ t hs.ne'
    have hr : 0 ≤ t - k * s := by linarith
    have hks0 : 0 ≤ (k : ℝ) * s := by positivity
    have e : T t w = T (t - k * s) (T (k * s) w) := by
      rw [← ContinuousLinearMap.comp_apply, ← hadd _ _ hr hks0]
      congr 2
      ring
    have h1 : ‖T t w‖ ≤ (q ^ ((1 / 2 : ℝ) ^ m)) ^ k * ‖w‖ := by
      rw [e]
      exact (hc _ hr _).trans (hmul s hs.le _ (by positivity) (hdy m) k w hw)
    have h2 : (q ^ ((1 / 2 : ℝ) ^ m)) ^ k = q ^ ((1 / 2 : ℝ) ^ m * k) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]
    have hsℓ : (1 / 2 : ℝ) ^ m = s / ℓ := by
      rw [hs_def, one_div_pow]
      field_simp
    have key : t - s ≤ s * k := by
      have := (div_lt_iff₀ hs).1 hlt
      nlinarith
    have h3 : t / ℓ - (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ m * k := by
      rw [hsℓ]
      calc t / ℓ - s / ℓ = (t - s) / ℓ := (sub_div t s ℓ).symm
        _ ≤ (s * k) / ℓ := by gcongr
        _ = s / ℓ * k := by ring
    calc ‖T t w‖ ≤ q ^ ((1 / 2 : ℝ) ^ m * k) * ‖w‖ := by rw [← h2]; exact h1
      _ ≤ q ^ (t / ℓ - (1 / 2 : ℝ) ^ m) * ‖w‖ :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hq hq1 h3) (norm_nonneg w)
  have hlim : Tendsto (fun m : ℕ => q ^ (t / ℓ - (1 / 2 : ℝ) ^ m) * ‖w‖) atTop
      (𝓝 (q ^ (t / ℓ) * ‖w‖)) := by
    have h1 : Tendsto (fun m : ℕ => t / ℓ - (1 / 2 : ℝ) ^ m) atTop (𝓝 (t / ℓ - 0)) :=
      tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    rw [sub_zero] at h1
    have h2 := ((Real.continuousAt_const_rpow hq.ne').tendsto).comp h1
    exact h2.mul_const _
  exact ge_of_tendsto' hlim hbound

end Decay

/-! ### Reconstruction data (NAMED HYPOTHESIS) -/

/-- **Reconstruction data** for the OS form `B` (the conclusion of the Osterwalder–Schrader
reconstruction theorem for the Hilbert space and the transfer semigroup — NOT proved here, used
only as an explicit hypothesis): a real Hilbert space `H`, the class map `cls : V → H`, and a
STRONGLY CONTINUOUS semigroup `T t` (`t ≥ 0`) of self-adjoint contractions fixing the vacuum, with
`⟨[F], T t [G]⟩ = B F G t`; the classes are dense (the reconstructed space is the completion of the
classes, so the vacuum is cyclic for `V` by construction). Such a semigroup is `T t = e^{-tH}` for a
self-adjoint `H ≥ 0` (standard semigroup theory, not formalised). Completeness and strong
continuity are required for this identification only: no theorem of this file uses them. -/
structure Recon (o : VecOps V) (B : V → V → ℝ → ℝ) where
  /-- The physical Hilbert space. -/
  H : Type
  [instNormed : NormedAddCommGroup H]
  [instInner : InnerProductSpace ℝ H]
  [instComplete : CompleteSpace H]
  /-- Class map `F ↦ [F]`. -/
  cls : V → H
  /-- Transfer semigroup `T t = e^{-tH}`. -/
  T : ℝ → H →L[ℝ] H
  inner_cls : ∀ F G, ⟪cls F, cls G⟫ = B F G 0
  inner_T : ∀ F G t, 0 ≤ t → ⟪cls F, T t (cls G)⟫ = B F G t
  T_add : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t)
  T_symm : ∀ t, 0 ≤ t → ∀ x y, ⟪T t x, y⟫ = ⟪x, T t y⟫
  T_contr : ∀ t, 0 ≤ t → ‖T t‖ ≤ 1
  T_vac : ∀ t, 0 ≤ t → T t (cls o.Ω) = cls o.Ω
  /-- Strong continuity at `0⁺` (with the semigroup law: a C₀-semigroup). -/
  T_cont : ∀ x, Tendsto (fun t => T t x) (𝓝[≥] 0) (𝓝 x)
  dense : DenseRange cls

attribute [instance] Recon.instNormed Recon.instInner Recon.instComplete

namespace Recon

variable {o : VecOps V} {B : V → V → ℝ → ℝ} (r : Recon o B)

/-- The vacuum vector `Ω = [vac]`. -/
def ω : r.H := r.cls o.Ω

lemma inner_ω_self (hΩ : B o.Ω o.Ω 0 = 1) : ⟪r.ω, r.ω⟫ = 1 := by
  rw [ω, r.inner_cls, hΩ]

lemma norm_cls (F : V) : ‖r.cls F‖ = Real.sqrt (B F F 0) := by
  rw [norm_eq_sqrt_real_inner, r.inner_cls]

lemma T_ω (t : ℝ) (ht : 0 ≤ t) : r.T t r.ω = r.ω := r.T_vac t ht

lemma inner_ω_T (t : ℝ) (ht : 0 ≤ t) (x : r.H) : ⟪r.ω, r.T t x⟫ = ⟪r.ω, x⟫ := by
  rw [← r.T_symm t ht, r.T_ω t ht]

lemma inner_ω_perp (hΩ : B o.Ω o.Ω 0 = 1) (x : r.H) : ⟪r.ω, x - ⟪r.ω, x⟫ • r.ω⟫ = 0 := by
  rw [inner_sub_right, real_inner_smul_right, r.inner_ω_self hΩ]
  ring

lemma norm_perp_le (hΩ : B o.Ω o.Ω 0 = 1) (x : r.H) : ‖x - ⟪r.ω, x⟫ • r.ω‖ ≤ ‖x‖ := by
  have h : ‖x - ⟪r.ω, x⟫ • r.ω‖ ^ 2 = ‖x‖ ^ 2 - ⟪r.ω, x⟫ ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, mul_pow, real_inner_smul_right, Real.norm_eq_abs, sq_abs,
      ← real_inner_self_eq_norm_sq r.ω, r.inner_ω_self hΩ, real_inner_comm r.ω x]
    ring
  have h2 : ‖x - ⟪r.ω, x⟫ • r.ω‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [h]
    nlinarith [sq_nonneg ⟪r.ω, x⟫]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

/-- Truncated correlation = matrix element of `e^{-tH}` between truncated vectors. -/
lemma corr_eq (hΩ : B o.Ω o.Ω 0 = 1) (F G : V) (t : ℝ) (ht : 0 ≤ t) :
    B F G t - B F o.Ω 0 * B o.Ω G 0 =
      ⟪r.cls F - ⟪r.ω, r.cls F⟫ • r.ω, r.T t (r.cls G - ⟪r.ω, r.cls G⟫ • r.ω)⟫ := by
  have h1 : B F G t = ⟪r.cls F, r.T t (r.cls G)⟫ := (r.inner_T F G t ht).symm
  have h2 : B F o.Ω 0 = ⟪r.cls F, r.ω⟫ := (r.inner_cls F o.Ω).symm
  have h3 : B o.Ω G 0 = ⟪r.ω, r.cls G⟫ := (r.inner_cls o.Ω G).symm
  rw [h1, h2, h3, map_sub, map_smul, r.T_ω t ht]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    r.inner_ω_T t ht, r.inner_ω_self hΩ]
  ring

/-- The q-bound, extended by density from the truncated classes to the whole of `Ω^⊥`. -/
lemma qbound {𝒜₀ : Set V} {ℓ q : ℝ} (hq : QGapOn o B 𝒜₀ ℓ q)
    (hd : ∀ w : r.H, ⟪r.ω, w⟫ = 0 → w ∈ closure (r.cls '' (o.trunc B '' 𝒜₀))) :
    ∀ w : r.H, ⟪r.ω, w⟫ = 0 → ⟪w, r.T ℓ w⟫ ≤ q * ‖w‖ ^ 2 := by
  intro w hw
  have hcl : IsClosed {x : r.H | ⟪x, r.T ℓ x⟫ ≤ q * ‖x‖ ^ 2} :=
    isClosed_le (continuous_id.inner (r.T ℓ).continuous)
      (continuous_const.mul (continuous_norm.pow 2))
  have hsub : r.cls '' (o.trunc B '' 𝒜₀) ⊆ {x : r.H | ⟪x, r.T ℓ x⟫ ≤ q * ‖x‖ ^ 2} := by
    rintro _ ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    show ⟪r.cls (o.trunc B A), r.T ℓ (r.cls (o.trunc B A))⟫ ≤ q * ‖r.cls (o.trunc B A)‖ ^ 2
    rw [r.inner_T _ _ ℓ hq.1.le, ← real_inner_self_eq_norm_sq, r.inner_cls]
    exact hq.2.2.2 A hA
  exact closure_minimal hsub hcl (hd w hw)

/-- **q-form ⟹ mass gap.** With the reconstruction (named hypothesis) and the density of the
truncated classes of `𝒜₀` in `Ω^⊥`, the q-form gives the mass gap `Δ = −log q / ℓ`. -/
theorem massGapOn_of_qGapOn (hΩ : B o.Ω o.Ω 0 = 1) {𝒜₀ : Set V} {ℓ q : ℝ}
    (hq : QGapOn o B 𝒜₀ ℓ q)
    (hd : ∀ w : r.H, ⟪r.ω, w⟫ = 0 → w ∈ closure (r.cls '' (o.trunc B '' 𝒜₀))) :
    MassGapOn o B Set.univ (-Real.log q / ℓ) := by
  have hb := r.qbound hq hd
  obtain ⟨hℓ, hq0, hq1, -⟩ := hq
  have hdec := decay_of_qbound r.T r.ω r.T_add r.T_symm r.T_contr (fun t ht => r.T_ω t ht)
    hℓ hq0 hq1.le hb
  refine ⟨div_pos (neg_pos.2 (Real.log_neg hq0 hq1)) hℓ, fun F _ G _ t ht => ?_⟩
  rw [r.corr_eq hΩ F G t ht]
  have hexp : Real.exp (-(-Real.log q / ℓ * t)) = q ^ (t / ℓ) := by
    rw [Real.rpow_def_of_pos hq0]
    congr 1
    field_simp
  rw [hexp, ← r.norm_cls F, ← r.norm_cls G]
  calc |⟪r.cls F - ⟪r.ω, r.cls F⟫ • r.ω, r.T t (r.cls G - ⟪r.ω, r.cls G⟫ • r.ω)⟫|
      ≤ ‖r.cls F - ⟪r.ω, r.cls F⟫ • r.ω‖ * ‖r.T t (r.cls G - ⟪r.ω, r.cls G⟫ • r.ω)‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ ‖r.cls F - ⟪r.ω, r.cls F⟫ • r.ω‖ * (q ^ (t / ℓ) * ‖r.cls G - ⟪r.ω, r.cls G⟫ • r.ω‖) :=
        mul_le_mul_of_nonneg_left (hdec t ht _ (r.inner_ω_perp hΩ _)) (norm_nonneg _)
    _ ≤ ‖r.cls F‖ * (q ^ (t / ℓ) * ‖r.cls G‖) := by
        gcongr
        · exact r.norm_perp_le hΩ _
        · exact r.norm_perp_le hΩ _
    _ = q ^ (t / ℓ) * ‖r.cls F‖ * ‖r.cls G‖ := by ring

/-- **Uniqueness of the vacuum is a consequence.** With the reconstruction and the density of the
truncated classes of `𝒜₀` in `Ω^⊥`, every vector fixed by `e^{-ℓH}` is a multiple of `Ω`. -/
theorem vacuum_unique (hΩ : B o.Ω o.Ω 0 = 1) {𝒜₀ : Set V} {ℓ q : ℝ} (hq : QGapOn o B 𝒜₀ ℓ q)
    (hd : ∀ w : r.H, ⟪r.ω, w⟫ = 0 → w ∈ closure (r.cls '' (o.trunc B '' 𝒜₀)))
    (w : r.H) (hw : r.T ℓ w = w) : w = ⟪r.ω, w⟫ • r.ω := by
  have hb := r.qbound hq hd
  have hperp : ⟪r.ω, w - ⟪r.ω, w⟫ • r.ω⟫ = 0 := r.inner_ω_perp hΩ w
  have hT : r.T ℓ (w - ⟪r.ω, w⟫ • r.ω) = w - ⟪r.ω, w⟫ • r.ω := by
    rw [map_sub, map_smul, hw, r.T_ω ℓ hq.1.le]
  have h1 := hb _ hperp
  rw [hT, real_inner_self_eq_norm_sq] at h1
  have h2 : ‖w - ⟪r.ω, w⟫ • r.ω‖ ^ 2 ≤ 0 := by
    have hq1 := hq.2.2.1
    nlinarith [sq_nonneg ‖w - ⟪r.ω, w⟫ • r.ω‖]
  have h3 : ‖w - ⟪r.ω, w⟫ • r.ω‖ = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm h2 (sq_nonneg _))
  exact sub_eq_zero.1 (norm_eq_zero.1 h3)

/-! #### Linearity of the class map and density of the truncated classes -/

lemma eq_of_inner_cls {x y : r.H} (h : ∀ F, ⟪r.cls F, x⟫ = ⟪r.cls F, y⟫) : x = y := by
  have hall : ∀ z : r.H, ⟪z, x - y⟫ = 0 := by
    intro z
    refine r.dense.induction_on (p := fun z => ⟪z, x - y⟫ = 0) z ?_ ?_
    · exact isClosed_eq (continuous_id.inner continuous_const) continuous_const
    · intro F
      rw [inner_sub_right, h F, sub_self]
  have h0 := hall (x - y)
  rw [real_inner_self_eq_norm_sq] at h0
  have : ‖x - y‖ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

lemma cls_add (hb : IsBilin o B) (F G : V) : r.cls (o.add F G) = r.cls F + r.cls G :=
  r.eq_of_inner_cls fun K => by
    rw [inner_add_right, r.inner_cls, r.inner_cls, r.inner_cls, hb.add_right]

lemma cls_smul (hb : IsBilin o B) (c : ℝ) (F : V) : r.cls (o.smul c F) = c • r.cls F :=
  r.eq_of_inner_cls fun K => by
    rw [real_inner_smul_right, r.inner_cls, r.inner_cls, hb.smul_right]

lemma cls_trunc (hb : IsBilin o B) (A : V) :
    r.cls (o.trunc B A) = r.cls A - ⟪r.ω, r.cls A⟫ • r.ω := by
  rw [VecOps.trunc, r.cls_add hb, r.cls_smul hb, ω, r.inner_cls, neg_smul, ← sub_eq_add_neg]

/-- For `𝒜₀ = univ` the density hypothesis is automatic (cyclicity of the vacuum is built into
the reconstruction). -/
lemma truncDense_univ (hb : IsBilin o B) :
    ∀ w : r.H, ⟪r.ω, w⟫ = 0 → w ∈ closure (r.cls '' (o.trunc B '' Set.univ)) := by
  intro w hw
  have hP : Continuous fun x : r.H => x - ⟪r.ω, x⟫ • r.ω :=
    continuous_id.sub ((continuous_const.inner continuous_id).smul continuous_const)
  have hPw : w - ⟪r.ω, w⟫ • r.ω = w := by rw [hw, zero_smul, sub_zero]
  have himg : (fun x : r.H => x - ⟪r.ω, x⟫ • r.ω) '' Set.range r.cls =
      r.cls '' (o.trunc B '' Set.univ) := by
    ext x
    constructor
    · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
      exact ⟨o.trunc B A, ⟨A, Set.mem_univ _, rfl⟩, r.cls_trunc hb A⟩
    · rintro ⟨_, ⟨A, -, rfl⟩, rfl⟩
      exact ⟨r.cls A, ⟨A, rfl⟩, (r.cls_trunc hb A).symm⟩
  rw [← himg, ← hPw]
  apply image_closure_subset_closure_image hP
  refine ⟨w, ?_, rfl⟩
  rw [r.dense.closure_range]
  exact Set.mem_univ _

/-! #### Operator form `‖e^{-tH}(1 − P_Ω)‖ ≤ e^{-Δt}` -/

/-- `1 − P_Ω`, with `P_Ω x = ⟨Ω, x⟩ Ω`. -/
def perp : r.H →L[ℝ] r.H := ContinuousLinearMap.id ℝ r.H - (innerSL ℝ r.ω).smulRight r.ω

lemma perp_apply (x : r.H) : r.perp x = x - ⟪r.ω, x⟫ • r.ω := by
  simp [perp, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

lemma corr_eq_perp (F G : V) (t : ℝ) (ht : 0 ≤ t) :
    B F G t - B F o.Ω 0 * B o.Ω G 0 = ⟪r.cls F, ((r.T t).comp r.perp) (r.cls G)⟫ := by
  rw [ContinuousLinearMap.comp_apply, r.perp_apply, map_sub, map_smul, r.T_ω t ht,
    inner_sub_right, real_inner_smul_right, r.inner_T F G t ht, ω, r.inner_cls, r.inner_cls]
  ring

/-- **Operator form.** With the reconstruction, `HasMassGap`-type decay of the truncated
correlations is equivalent to `‖e^{-tH}(1 − P_Ω)‖ ≤ e^{-Δt}` for every `t ≥ 0`. -/
theorem massGapOn_univ_iff_opNorm (hΩ : B o.Ω o.Ω 0 = 1) (Δ : ℝ) :
    MassGapOn o B Set.univ Δ ↔
      0 < Δ ∧ ∀ t, 0 ≤ t → ‖(r.T t).comp r.perp‖ ≤ Real.exp (-(Δ * t)) := by
  constructor
  · rintro ⟨hΔ, h⟩
    refine ⟨hΔ, fun t ht => ?_⟩
    have hc : 0 ≤ Real.exp (-(Δ * t)) := (Real.exp_pos _).le
    have hcls : ∀ F G : V, |⟪r.cls F, ((r.T t).comp r.perp) (r.cls G)⟫| ≤
        Real.exp (-(Δ * t)) * ‖r.cls F‖ * ‖r.cls G‖ := by
      intro F G
      rw [← r.corr_eq_perp F G t ht, r.norm_cls, r.norm_cls]
      exact h F (Set.mem_univ _) G (Set.mem_univ _) t ht
    have hall : ∀ x y : r.H, |⟪x, ((r.T t).comp r.perp) y⟫| ≤
        Real.exp (-(Δ * t)) * ‖x‖ * ‖y‖ := by
      intro x y
      refine r.dense.induction_on
        (p := fun y => |⟪x, ((r.T t).comp r.perp) y⟫| ≤ Real.exp (-(Δ * t)) * ‖x‖ * ‖y‖) y ?_ ?_
      · exact isClosed_le (continuous_const.inner ((r.T t).comp r.perp).continuous).abs
          (continuous_const.mul continuous_norm)
      · intro G
        refine r.dense.induction_on (p := fun x => |⟪x, ((r.T t).comp r.perp) (r.cls G)⟫| ≤
          Real.exp (-(Δ * t)) * ‖x‖ * ‖r.cls G‖) x ?_ ?_
        · exact isClosed_le (continuous_id.inner continuous_const).abs
            ((continuous_const.mul continuous_norm).mul continuous_const)
        · intro F
          exact hcls F G
    refine ContinuousLinearMap.opNorm_le_bound _ hc fun y => ?_
    have h1 := hall (((r.T t).comp r.perp) y) y
    rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at h1
    by_contra hcon
    push Not at hcon
    nlinarith [norm_nonneg (((r.T t).comp r.perp) y), mul_nonneg hc (norm_nonneg y)]
  · rintro ⟨hΔ, h⟩
    refine ⟨hΔ, fun F _ G _ t ht => ?_⟩
    rw [r.corr_eq_perp F G t ht, ← r.norm_cls F, ← r.norm_cls G]
    calc |⟪r.cls F, ((r.T t).comp r.perp) (r.cls G)⟫|
        ≤ ‖r.cls F‖ * ‖((r.T t).comp r.perp) (r.cls G)‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖r.cls F‖ * (‖(r.T t).comp r.perp‖ * ‖r.cls G‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ ‖r.cls F‖ * (Real.exp (-(Δ * t)) * ‖r.cls G‖) := by
          gcongr
          exact h t ht
      _ = Real.exp (-(Δ * t)) * ‖r.cls F‖ * ‖r.cls G‖ := by ring

end Recon

end ClayYM.Transfer
