/-
ClayYM/Fake/Products.lean
=========================
Mechanism of the counterexample found by the adversarial review against the former variant B: for
two DECOUPLED sectors (sum of independent fields, `indepSum`), the CONNECTED two-point functions
add up (`conn2_indepSum`); hence `κ` (FP1) and `C_T` (FP3) add up, and
`YM_SU(2) ⊗ (12(dim G − 3) massive free scalars)` or `YM_{G₁} ⊗ YM_{G₂}` mimic the fingerprint
of a group of dimension `dim G`. Hence the clause `indecomposable` of `YMFingerprint` and the
imposed coefficient `κ`.

Checks of the definition of `Decomposable`:
* `indepSum_trivS_left`: a trivial factor gives back the theory itself; this is why each
  factor must have a non-zero connected correlation (`HasConnected`), otherwise EVERY theory would
  be "decomposable" and the statement would be unsatisfiable;
* `not_hasConnected_trivS`: the trivial theory has no connected correlation.
-/
import ClayYM.Fake.TrivialAB

open MeasureTheory Filter Topology

noncomputable section

namespace ClayYM

lemma subList_eq_nil_iff {α : Type} (l : List α) (s : Fin l.length → Bool) :
    subList l s = [] ↔ ∀ k, s k = false := by
  simp [subList, List.filter_eq_nil_iff]

lemma subList_all {α : Type} (l : List α) : subList l (fun _ => true) = l := by
  simp [subList, List.map_get_finRange]

lemma sum_fin1_bool (f : (Fin 1 → Bool) → ℝ) :
    ∑ s, f s = f (fun _ => true) + f (fun _ => false) := by
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) Bool) f (fun b => f (fun _ => b))
    (fun s => by congr 1; funext k; fin_cases k; rfl)]
  simp [Fintype.sum_bool]

lemma sum_fin2_bool (f : (Fin 2 → Bool) → ℝ) :
    ∑ s, f s = f ![true, true] + f ![true, false] + f ![false, true] + f ![false, false] := by
  rw [Fintype.sum_equiv (finTwoArrowEquiv Bool) f (fun b => f ![b.1, b.2])
    (fun s => by congr 1; funext k; fin_cases k <;> rfl)]
  simp [Fintype.sum_prod_type, Fintype.sum_bool]
  ring

lemma subList_two {α : Type} (p q : α) (b₀ b₁ : Bool) :
    subList [p, q] ![b₀, b₁] = (if b₀ then [p] else []) ++ (if b₁ then [q] else []) := by
  cases b₀ <;> cases b₁ <;> rfl

lemma not_mask_two (b₀ b₁ : Bool) : (fun k => !((![b₀, b₁] : Fin 2 → Bool) k)) = ![!b₀, !b₁] := by
  funext k; fin_cases k <;> rfl

/-- A trivial factor gives back the theory: `indepSum triv S = S`. -/
theorem indepSum_trivS_left (S : Schwinger YMIdx 4) (l : LList YMIdx 4) :
    indepSum (trivS YMIdx 4) S l = S l := by
  unfold indepSum
  rw [Finset.sum_eq_single (fun _ => false)]
  · have h1 : subList l (fun _ => false) = [] := (subList_eq_nil_iff l _).mpr (fun _ => rfl)
    simp only [h1, Bool.not_false, subList_all]
    simp [trivS]
  · intro s _ hs
    have hne : subList l s ≠ [] := by
      rw [Ne, subList_eq_nil_iff]
      intro hall
      exact hs (funext hall)
    simp [trivS, hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The trivial theory has no connected correlation. -/
theorem not_hasConnected_trivS : ¬ HasConnected (trivS YMIdx 4) := by
  rintro ⟨c, c', x, -, hx⟩
  exact hx (conn2_trivS c c' x 0)

/-- One-point functions of an independent sum. -/
lemma sub1_t {α : Type} (p : α) : subList [p] (fun _ : Fin 1 => true) = [p] := rfl
lemma sub1_f {α : Type} (p : α) : subList [p] (fun _ : Fin 1 => false) = [] := rfl
lemma sub1c_t {α : Type} (p : α) :
    subList [p] (fun k : Fin [p].length => !((fun _ : Fin 1 => true) k)) = [] := rfl
lemma sub1c_f {α : Type} (p : α) :
    subList [p] (fun k : Fin [p].length => !((fun _ : Fin 1 => false) k)) = [p] := rfl

lemma indepSum_one (S₁ S₂ : Schwinger YMIdx 4) (h₁ : S₁ [] = 1) (h₂ : S₂ [] = 1)
    (p : YMIdx × Spacetime 4) : indepSum S₁ S₂ [p] = S₁ [p] + S₂ [p] := by
  unfold indepSum
  change (∑ s : Fin 1 → Bool, S₁ (subList [p] s) * S₂ (subList [p] fun k => !s k)) = _
  rw [sum_fin1_bool, sub1_t, sub1_f, sub1c_t, sub1c_f, h₁, h₂, mul_one, one_mul]

lemma sub2_tt {α : Type} (p q : α) : subList [p, q] (![true, true] : Fin 2 → Bool) = [p, q] := rfl
lemma sub2c_tt {α : Type} (p q : α) :
    subList [p, q] (fun k : Fin [p, q].length => !((![true, true] : Fin 2 → Bool) k)) = [] := rfl
lemma sub2_tf {α : Type} (p q : α) : subList [p, q] (![true, false] : Fin 2 → Bool) = [p] := rfl
lemma sub2c_tf {α : Type} (p q : α) :
    subList [p, q] (fun k : Fin [p, q].length => !((![true, false] : Fin 2 → Bool) k)) = [q] := rfl
lemma sub2_ft {α : Type} (p q : α) : subList [p, q] (![false, true] : Fin 2 → Bool) = [q] := rfl
lemma sub2c_ft {α : Type} (p q : α) :
    subList [p, q] (fun k : Fin [p, q].length => !((![false, true] : Fin 2 → Bool) k)) = [p] := rfl
lemma sub2_ff {α : Type} (p q : α) : subList [p, q] (![false, false] : Fin 2 → Bool) = [] := rfl
lemma sub2c_ff {α : Type} (p q : α) :
    subList [p, q] (fun k : Fin [p, q].length => !((![false, false] : Fin 2 → Bool) k)) = [p, q] := rfl

lemma indepSum_two (S₁ S₂ : Schwinger YMIdx 4) (h₁ : S₁ [] = 1) (h₂ : S₂ [] = 1)
    (p q : YMIdx × Spacetime 4) :
    indepSum S₁ S₂ [p, q] = S₁ [p, q] + S₁ [p] * S₂ [q] + S₁ [q] * S₂ [p] + S₂ [p, q] := by
  unfold indepSum
  change (∑ s : Fin 2 → Bool, S₁ (subList [p, q] s) * S₂ (subList [p, q] fun k => !s k)) = _
  rw [sum_fin2_bool, sub2_tt, sub2_tf, sub2_ft, sub2_ff, sub2c_tt, sub2c_tf, sub2c_ft, sub2c_ff,
    h₁, h₂]
  ring

/-- **Additivity**: the connected two-point function of a sum of decoupled sectors is the
sum of the connected functions of the sectors. -/
theorem conn2_indepSum (S₁ S₂ : Schwinger YMIdx 4) (h₁ : S₁ [] = 1) (h₂ : S₂ [] = 1)
    (c c' : Coef) (x y : Spacetime 4) :
    conn2 (indepSum S₁ S₂) c c' x y = conn2 S₁ c c' x y + conn2 S₂ c c' x y := by
  simp only [conn2, S2, S1, indepSum_one S₁ S₂ h₁ h₂, indepSum_two S₁ S₂ h₁ h₂]
  simp only [mul_add, Finset.sum_add_distrib]
  have e1 : ∀ (u : Coef) (z : Spacetime 4), (∑ a, u a * S₁ [(a, z)]) = ∑ a, u a * S₁ [(a, z)] :=
    fun _ _ => rfl
  rw [show (∑ a, ∑ b, c a * c' b * (S₁ [(a, x)] * S₂ [(b, y)])) =
      (∑ a, c a * S₁ [(a, x)]) * (∑ b, c' b * S₂ [(b, y)]) by
        rw [Finset.sum_mul_sum]; refine Finset.sum_congr rfl (fun a _ => ?_)
        refine Finset.sum_congr rfl (fun b _ => ?_); ring]
  rw [show (∑ a, ∑ b, c a * c' b * (S₁ [(b, y)] * S₂ [(a, x)])) =
      (∑ a, c a * S₂ [(a, x)]) * (∑ b, c' b * S₁ [(b, y)]) by
        rw [Finset.sum_mul_sum]; refine Finset.sum_congr rfl (fun a _ => ?_)
        refine Finset.sum_congr rfl (fun b _ => ?_); ring]
  ring

/-! ### Mutation test of `indecomposable`: the UV fingerprint is ADDITIVE

If two decoupled sectors each carry the UV fingerprint (FP1–FP3) of a group `K₁`, resp. `K₂`, their
sum carries that of every group `K` with `dim K = dim K₁ + dim K₂` (for example
`dim SU(5) = 24 = dim SU(2) + dim Spin(7)`). FP1–FP3 therefore CANNOT exclude products: the
clause `indecomposable` is necessary. (That the product of two OS theories with a mass gap is an
OS theory with a mass gap, with `T = T₁ + T₂` conserved and Ward-normalised, is standard but is
not formalised here.) -/

theorem traceAnomalyCoeff_add (K K₁ K₂ : CompactSimpleGroup)
    (hdim : (K.dim : ℝ) = K₁.dim + K₂.dim) :
    traceAnomalyCoeff K = traceAnomalyCoeff K₁ + traceAnomalyCoeff K₂ := by
  unfold traceAnomalyCoeff
  rw [hdim]
  ring

lemma uvg_indepSum (S₁ S₂ : Schwinger YMIdx 4) (h₁ : S₁ [] = 1) (h₂ : S₂ [] = 1) (z₁ z₂ : ℝ)
    (x : Spacetime 4) :
    ‖x‖ ^ 8 * conn2 (indepSum S₁ S₂) (θc z₁ z₂) (θc z₁ z₂) x 0 * (Real.log ‖x‖) ^ 2 =
      ‖x‖ ^ 8 * conn2 S₁ (θc z₁ z₂) (θc z₁ z₂) x 0 * (Real.log ‖x‖) ^ 2 +
      ‖x‖ ^ 8 * conn2 S₂ (θc z₁ z₂) (θc z₁ z₂) x 0 * (Real.log ‖x‖) ^ 2 := by
  rw [conn2_indepSum S₁ S₂ h₁ h₂]
  ring

/-- **FP1 + FP2 additive**: `κ` adds up, the FP2 correction (a ratio) is unchanged. -/
theorem UVTrace_indepSum (S₁ S₂ : Schwinger YMIdx 4) (h₁ : S₁ [] = 1) (h₂ : S₂ [] = 1)
    (z₁ z₂ κ₁ κ₂ : ℝ) (hκ₁ : 0 < κ₁) (hκ₂ : 0 < κ₂)
    (hT₁ : UVTrace S₁ z₁ z₂ κ₁) (hT₂ : UVTrace S₂ z₁ z₂ κ₂) :
    UVTrace (indepSum S₁ S₂) z₁ z₂ (κ₁ + κ₂) := by
  obtain ⟨a₁, b₁⟩ := hT₁
  obtain ⟨a₂, b₂⟩ := hT₂
  have hs : κ₁ + κ₂ ≠ 0 := (add_pos hκ₁ hκ₂).ne'
  have hid : ∀ g₁ g₂ : ℝ, (g₁ + g₂) / (κ₁ + κ₂) - 1 =
      κ₁ / (κ₁ + κ₂) * (g₁ / κ₁ - 1) + κ₂ / (κ₁ + κ₂) * (g₂ / κ₂ - 1) := by
    intro g₁ g₂
    field_simp
    ring
  have hlim : κ₁ / (κ₁ + κ₂) * (-(102 / 121 : ℝ)) + κ₂ / (κ₁ + κ₂) * (-(102 / 121)) =
      -(102 / 121) := by
    field_simp
    ring
  constructor
  · refine (a₁.add a₂).congr (fun x => ?_)
    beta_reduce
    rw [uvg_indepSum S₁ S₂ h₁ h₂ z₁ z₂ x]
  · have hb := (b₁.const_mul (κ₁ / (κ₁ + κ₂))).add (b₂.const_mul (κ₂ / (κ₁ + κ₂)))
    rw [hlim] at hb
    refine hb.congr (fun x => ?_)
    beta_reduce
    rw [uvg_indepSum S₁ S₂ h₁ h₂ z₁ z₂ x, hid]
    ring

/-- **FP3 additive**: `C_T` adds up. -/
theorem UVStress_indepSum (K K₁ K₂ : CompactSimpleGroup) (S₁ S₂ : Schwinger YMIdx 4)
    (h₁ : S₁ [] = 1) (h₂ : S₂ [] = 1) (z₁ z₂ : ℝ) (hdim : (K.dim : ℝ) = K₁.dim + K₂.dim)
    (hU₁ : UVStress K₁ S₁ z₁ z₂) (hU₂ : UVStress K₂ S₂ z₁ z₂) :
    UVStress K (indepSum S₁ S₂) z₁ z₂ := by
  intro u hu μ ν ρ σ
  have h := (hU₁ u hu μ ν ρ σ).add (hU₂ u hu μ ν ρ σ)
  have hval : (K₁.dim : ℝ) * (4 / Real.pi ^ 4) * confI u μ ν ρ σ +
      (K₂.dim : ℝ) * (4 / Real.pi ^ 4) * confI u μ ν ρ σ =
      (K.dim : ℝ) * (4 / Real.pi ^ 4) * confI u μ ν ρ σ := by
    rw [hdim]
    ring
  rw [hval] at h
  refine h.congr (fun s => ?_)
  beta_reduce
  rw [conn2_indepSum S₁ S₂ h₁ h₂]
  ring

/-- **Mutation test of `indecomposable`.** The full UV fingerprint (FP1 with imposed `κ`, FP2,
FP3) of a decoupled sum is that of the group whose dimension is the sum. -/
theorem uvFingerprint_indepSum (K K₁ K₂ : CompactSimpleGroup) (S₁ S₂ : Schwinger YMIdx 4)
    (h₁ : S₁ [] = 1) (h₂ : S₂ [] = 1) (z₁ z₂ : ℝ) (hdim : (K.dim : ℝ) = K₁.dim + K₂.dim)
    (hT₁ : UVTrace S₁ z₁ z₂ (traceAnomalyCoeff K₁)) (hU₁ : UVStress K₁ S₁ z₁ z₂)
    (hT₂ : UVTrace S₂ z₁ z₂ (traceAnomalyCoeff K₂)) (hU₂ : UVStress K₂ S₂ z₁ z₂) :
    UVTrace (indepSum S₁ S₂) z₁ z₂ (traceAnomalyCoeff K) ∧
      UVStress K (indepSum S₁ S₂) z₁ z₂ := by
  refine ⟨?_, UVStress_indepSum K K₁ K₂ S₁ S₂ h₁ h₂ z₁ z₂ hdim hU₁ hU₂⟩
  rw [traceAnomalyCoeff_add K K₁ K₂ hdim]
  exact UVTrace_indepSum S₁ S₂ h₁ h₂ z₁ z₂ _ _ (traceAnomalyCoeff_pos K₁)
    (traceAnomalyCoeff_pos K₂) hT₁ hT₂

/-- **"Products" guard.** Every decoupled sum of two OS theories that each have a non-zero connected
correlation is rejected by `YMFingerprint` (clause `indecomposable`), whatever its UV data: in
particular `YM_{G₁} ⊗ YM_{G₂}` and `YM_G ⊗ free matter`. -/
theorem indepSum_not_YMFingerprint (K : CompactSimpleGroup) (S₁ S₂ : Schwinger YMIdx 4)
    (hOS₁ : OSAxioms tensorRep4 S₁) (hOS₂ : OSAxioms tensorRep4 S₂)
    (hc₁ : HasConnected S₁) (hc₂ : HasConnected S₂) :
    ¬ YMFingerprint K (indepSum S₁ S₂) := fun h =>
  h.indecomposable ⟨S₁, S₂, hOS₁, hOS₂, hc₁, hc₂, fun _ _ => rfl⟩

end ClayYM
