/-
ClayYM/Fake/TrivialAB.lean
==========================
The trivial theory against variants A and B (mutation tests).

Variant A: for EVERY group `K`, the trivial theory is the limit of the GENUINE Wilson measures of
`K` with the renormalisation `Z = 0, c = 0` (`trivial_wilson_limit`): it satisfies OS, the tensor
symmetries, lattice convergence and the mass gap for every `Δ`. It is rejected ONLY by
`finite_mass` (m < ∞) and `components_nontrivial` ⟹ these two clauses are necessary.

Variant B: the trivial theory satisfies the tensor symmetries, conservation and the Ward identity
(for all `z₁, z₂`), but violates FP1 (`UVTrace`) and `FiniteMass`.
-/
import ClayYM.Fake.Trivial
import ClayYM.Fake.Lemmas

open MeasureTheory Filter Topology

noncomputable section

namespace ClayYM

/-- `S1` of a trivial theory is zero (the list contains at least one point). -/
lemma S1_trivS (c : Coef) (x : Spacetime 4) (rest : LList YMIdx 4) :
    S1 (trivS YMIdx 4) c x rest = 0 := by
  simp [S1, trivS]

lemma S2_trivS (c c' : Coef) (x y : Spacetime 4) : S2 (trivS YMIdx 4) c c' x y = 0 := by
  simp [S2, trivS]

lemma conn2_trivS (c c' : Coef) (x y : Spacetime 4) : conn2 (trivS YMIdx 4) c c' x y = 0 := by
  simp [conn2, S1_trivS, S2_trivS]

theorem trivS_TensorSymmetric : TensorSymmetric (trivS YMIdx 4) := by
  intro n i x k _
  have hn : n ≠ 0 := fun h => (h ▸ k).elim0
  simp [trivS_mkList, hn]

theorem trivS_Conserved (z₁ z₂ : ℝ) : Conserved (trivS YMIdx 4) z₁ z₂ := by
  intro ν n i y x _ _
  simp [S1_trivS, lineDeriv]

lemma rpKernelIns_trivS (c : Coef) (p : Spacetime 4) (a b : Term YMIdx 4)
    (x : Config 4 a.n) (y : Config 4 b.n) : rpKernelIns (trivS YMIdx 4) c p a b x y = 0 := by
  simp [rpKernelIns, S1_trivS, trivS]

lemma rpFormIns_trivS (c : Coef) (p : Spacetime 4) (F G : Family YMIdx 4) :
    rpFormIns (trivS YMIdx 4) c p F G = 0 := by
  simp [rpFormIns, rpKernelIns_trivS]

theorem trivS_WardEnergy (z₁ z₂ : ℝ) : WardEnergy (trivS YMIdx 4) z₁ z₂ := by
  intro F G
  simp only [rpFormIns_trivS, integral_zero]
  refine ⟨integrable_zero _ _ _, ?_⟩
  have : (fun t => rpForm tensorRep4 (trivS YMIdx 4) F G t) = fun _ => trivAmp F * trivAmp G := by
    funext t; exact rpForm_trivS tensorRep4 F G t
  rw [this]
  exact hasDerivAt_const 0 _

theorem trivS_not_UVTrace (z₁ z₂ κ : ℝ) (hκ : κ ≠ 0) : ¬ UVTrace (trivS YMIdx 4) z₁ z₂ κ :=
  not_UVTrace_of_zero _ z₁ z₂ κ hκ (fun x _ => conn2_trivS _ _ x 0)

theorem trivS_not_YMFingerprint (K : CompactSimpleGroup) :
    ¬ YMFingerprint K (trivS YMIdx 4) := by
  rintro ⟨-, ⟨z₁, z₂, -, -, -, hT, -⟩, -⟩
  exact trivS_not_UVTrace z₁ z₂ _ (traceAnomalyCoeff_pos K).ne' hT

theorem trivS_not_ComponentsNontrivial : ¬ ComponentsNontrivial (trivS YMIdx 4) := by
  intro h
  obtain ⟨x, -, hx⟩ := h (0, 1, 0, 1) (by decide) (by decide)
  exact hx (conn2_trivS _ _ x 0)

/-- The trivial theory does not satisfy variant B (for any group). -/
theorem trivS_not_B (K : CompactSimpleGroup) :
    ¬ (OSAxioms tensorRep4 (trivS YMIdx 4) ∧ ClayMassGap tensorRep4 (trivS YMIdx 4) ∧
      ComponentsNontrivial (trivS YMIdx 4) ∧ YMFingerprint K (trivS YMIdx 4)) :=
  fun h => trivS_not_YMFingerprint K h.2.2.2

/-! ### Variant A: the trivial limit of the genuine Wilson measures -/

/-- An explicit sequence of lattices: `a_k = 1/(k+1)`, side `L_k + 1 = k(k+1) + 1`, `β_k = k`. -/
def exampleSeq : LatticeSeq where
  a := fun k => 1 / ((k : ℝ) + 1)
  L := fun k => k * (k + 1)
  β := fun k => (k : ℝ)
  a_pos := fun k => by positivity
  a_lim := tendsto_one_div_add_atTop_nhds_zero_nat
  vol_lim := by
    refine tendsto_atTop_mono (fun k => ?_) tendsto_natCast_atTop_atTop
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    show (k : ℝ) ≤ (((k * (k + 1) : ℕ) : ℝ) + 1) * (1 / ((k : ℝ) + 1))
    rw [mul_one_div, le_div_iff₀ hk]
    push_cast
    nlinarith
  β_lim := tendsto_natCast_atTop_atTop

section ZeroField

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] {N : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin N) ℂ)

lemma latticeExpect_zero (L : ℕ) (β : ℝ) : latticeExpect ρ L β (fun _ => 0) = 0 := by
  simp [latticeExpect]

lemma renField_zero {L : ℕ} (a : ℝ) (U : LinkConfig G L) (x : Site L) (α : YMIdx) :
    renField ρ a 0 0 U x α = 0 := by
  simp only [renField, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, Pi.zero_apply, sub_zero]

/-- Smeared correlations of an identically zero field: zero for `n ≥ 1`. -/
lemma latSmeared_eq_zero {α : Type} (L : ℕ) (a β : ℝ)
    (φ : LinkConfig G L → Site L → α → ℝ) (hφ : ∀ U y j, φ U y j = 0)
    (n : ℕ) (hn : 0 < n) (i : Fin n → α) (f : Config 4 n → ℝ) :
    latSmeared ρ L a β φ n i f = 0 := by
  unfold latSmeared
  have h : ∀ y : Fin n → Site L, latticeExpect ρ L β (fun U => ∏ k, φ U (y k) (i k)) = 0 := by
    intro y
    have h0 : (fun U => ∏ k, φ U (y k) (i k)) = fun _ => (0 : ℝ) := by
      funext U
      exact Finset.prod_eq_zero (Finset.mem_univ ⟨0, hn⟩) (hφ _ _ _)
    rw [h0]
    exact latticeExpect_zero ρ L β
  simp [h]

end ZeroField

/-- For every group `K` (and the representation `K.ρ` in the Wilson action), the trivial
theory is a limit of the Wilson measures of `K` (renormalisation `Z = 0`, `c = 0`) and satisfies
all the clauses of variant A that concern the limit theory, EXCEPT `finite_mass` and
`components_nontrivial`. -/
theorem trivial_wilson_limit (K : CompactSimpleGroup) :
    ∃ (sq : LatticeSeq) (Z : ℕ → Matrix YMIdx YMIdx ℝ) (c : ℕ → YMIdx → ℝ),
      OSAxioms tensorRep4 (trivS YMIdx 4) ∧ TensorSymmetric (trivS YMIdx 4) ∧
      LatticeConverges K.ρ sq (fun k U y α => renField K.ρ (sq.a k) (Z k) (c k) U y α)
        (trivS YMIdx 4) ∧
      (∀ Δ : ℝ, 0 < Δ → HasMassGap tensorRep4 (trivS YMIdx 4) Δ) ∧
      ¬ FiniteMass tensorRep4 (trivS YMIdx 4) ∧ ¬ ComponentsNontrivial (trivS YMIdx 4) := by
  refine ⟨exampleSeq, fun _ => 0, fun _ => 0, trivS_OSAxioms _, trivS_TensorSymmetric, ?_,
    fun Δ hΔ => trivS_hasMassGap _ hΔ, trivS_not_finiteMass _, trivS_not_ComponentsNontrivial⟩
  intro n hn i f _
  have hrhs : (∫ x, f x * trivS YMIdx 4 (mkList i x)) = 0 := by
    simp [trivS_mkList, hn.ne']
  rw [hrhs]
  refine tendsto_const_nhds.congr (fun k => ?_)
  exact (latSmeared_eq_zero K.ρ _ _ _ _ (fun U y j => renField_zero K.ρ _ U y j) n hn i f).symm

end ClayYM
