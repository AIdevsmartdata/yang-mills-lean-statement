/-
ClayYM/Fake/Trivial.lean
========================
FAKE MODEL no. 1: the trivial theory `S(∅) = 1`, `S(l) = 0` otherwise (reconstructed Hilbert space
`= ℂΩ`). Proved results (no `sorry`):

* `trivS_OSAxioms`      : it satisfies ALL the Osterwalder–Schrader axioms, for every
                          representation `R` — so the axiom system `OSAxioms` is not
                          contradictory (unlike the pre-09/2026 vacuum axiom of the lean-dojo
                          repository, which made the structure empty);
* `trivS_hasMassGap`    : EVERY `Δ > 0` is a mass gap;
* `trivS_not_finiteMass`: it violates "m < ∞" (Jaffe–Witten §4).

Conclusion (mutation test): the clause `FiniteMass` is NECESSARY; without it, the
"OS + mass gap" part of the statement would be satisfied by the trivial theory.
-/
import ClayYM.Gap

open scoped ContDiff BigOperators
open MeasureTheory Filter Topology

noncomputable section

namespace ClayYM

variable {ι : Type} {d : ℕ}

/-- The trivial theory. -/
def trivS (ι : Type) (d : ℕ) : Schwinger ι d := fun l => if l = [] then 1 else 0

lemma trivS_append (l l' : LList ι d) :
    trivS ι d (l ++ l') = trivS ι d l * trivS ι d l' := by
  unfold trivS
  by_cases h : l = [] <;> by_cases h' : l' = [] <;> simp [h, h']

lemma trivS_mkList {n : ℕ} (i : Fin n → ι) (x : Config d n) :
    trivS ι d (mkList i x) = if n = 0 then 1 else 0 := by
  unfold trivS mkList
  simp [List.ofFn_eq_nil_iff]

lemma trivS_shiftList (a : Spacetime d) (l : LList ι d) :
    trivS ι d (shiftList a l) = trivS ι d l := by
  unfold trivS shiftList
  simp

/-- Indicator of "term without points". -/
def c0 {n : ℕ} : ℝ := if n = 0 then 1 else 0

lemma sum_reflect_c0 [Fintype ι] {n : ℕ} (M : Matrix ι ι ℝ) (lab : Fin n → ι) (c : ℝ) :
    (∑ j : Fin n → ι, (∏ k, M (lab (Fin.rev k)) (j k)) * ((if n = 0 then (1:ℝ) else 0) * c)) =
      (if n = 0 then (1:ℝ) else 0) * c := by
  cases n with
  | zero => simp
  | succ n => simp

lemma rpKernel_trivS [Fintype ι] [NeZero d] (R : CompRep ι d) (a b : Term ι d) (t : ℝ)
    (x : Config d a.n) (y : Config d b.n) :
    rpKernel R (trivS ι d) a b t x y =
      (if a.n = 0 then (1:ℝ) else 0) * (if b.n = 0 then (1:ℝ) else 0) := by
  obtain ⟨n, la, fa⟩ := a
  obtain ⟨m, lb, fb⟩ := b
  simp only [rpKernel, trivS_append, trivS_mkList]
  exact sum_reflect_c0 (R (θ d)) la _

/-- "Amplitude" of a family in the trivial theory: the component along `Ω`. -/
def trivAmp [NeZero d] (F : Family ι d) : ℝ :=
  (F.map fun a => (if a.n = 0 then (1:ℝ) else 0) * ∫ x, a.f x).sum

lemma integral_prod_const {n m : ℕ} (f : Config d n → ℝ) (g : Config d m → ℝ) (k : ℝ) :
    (∫ x, ∫ y, f x * g y * k) = (∫ x, f x) * (∫ y, g y) * k := by
  have h1 : ∀ x, (∫ y, f x * g y * k) = (f x * k) * ∫ y, g y := by
    intro x
    rw [← integral_const_mul]
    congr 1; ext y; ring
  simp_rw [h1]
  rw [integral_mul_const, integral_mul_const]
  ring

lemma rpForm_trivS [Fintype ι] [NeZero d] (R : CompRep ι d) (F G : Family ι d) (t : ℝ) :
    rpForm R (trivS ι d) F G t = trivAmp F * trivAmp G := by
  unfold rpForm trivAmp
  simp only [rpKernel_trivS]
  have key : ∀ a b : Term ι d,
      (∫ x, ∫ y, a.f x * b.f y *
        ((if a.n = 0 then (1:ℝ) else 0) * (if b.n = 0 then (1:ℝ) else 0))) =
      ((if a.n = 0 then (1:ℝ) else 0) * ∫ x, a.f x) *
        ((if b.n = 0 then (1:ℝ) else 0) * ∫ y, b.f y) := by
    intro a b
    rw [integral_prod_const]
    ring
  simp_rw [key, List.sum_map_mul_left, List.sum_map_mul_right]

lemma volume_config_zero_univ : (volume : Measure (Config d 0)) Set.univ = 1 := by
  rw [volume_pi, Measure.pi_univ]
  simp

lemma volume_real_config_zero_univ : (volume : Measure (Config d 0)).real Set.univ = 1 := by
  rw [measureReal_def, volume_config_zero_univ]
  simp

lemma trivAmp_vac [NeZero d] : trivAmp (vac ι : Family ι d) = 1 := by
  simp only [trivAmp, vac, vacTerm, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  simp [vacTest, volume_real_config_zero_univ]

/-- The trivial theory satisfies all the OS axioms (for every representation `R`). -/
theorem trivS_OSAxioms [Fintype ι] [NeZero d] (R : CompRep ι d) :
    OSAxioms R (trivS ι d) where
  normalized := by simp [trivS]
  smooth := by
    intro n i
    simp only [trivS_mkList]
    exact contDiffOn_const
  linear_growth := by
    refine ⟨1, 0, 0, one_pos, le_rfl, le_rfl, ?_⟩
    intro n i x _
    rw [trivS_mkList, zero_mul, Real.rpow_zero, Real.rpow_zero, mul_one, mul_one]
    split_ifs <;> norm_num
  translation_invariant := by
    intro a l _
    exact trivS_shiftList a l
  rotation_covariant := by
    intro g n i x _
    simp only [trivS_mkList]
    cases n with
    | zero => simp
    | succ n => simp
  symmetric := by
    intro l l' h
    unfold trivS
    by_cases hl : l = []
    · subst hl
      have : l' = [] := List.Perm.eq_nil h.symm
      simp [this]
    · have : l' ≠ [] := fun h' => hl (List.Perm.eq_nil (h' ▸ h))
      simp [hl, this]
  reflection_positive := by
    intro F
    rw [rpForm_trivS]
    exact mul_self_nonneg _
  cluster := by
    intro l l' a _ _ _ _
    simp only [trivS_append, trivS_shiftList]
    exact tendsto_const_nhds

/-- Every `Δ > 0` is a mass gap of the trivial theory. -/
theorem trivS_hasMassGap [Fintype ι] [NeZero d] (R : CompRep ι d) {Δ : ℝ} (hΔ : 0 < Δ) :
    HasMassGap R (trivS ι d) Δ := by
  refine ⟨hΔ, fun F G t _ => ?_⟩
  simp only [rpForm_trivS, trivAmp_vac, mul_one, one_mul, sub_self, abs_zero]
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

/-- The trivial theory violates "m < ∞". -/
theorem trivS_not_finiteMass [Fintype ι] [NeZero d] (R : CompRep ι d) :
    ¬ FiniteMass R (trivS ι d) := by
  rintro ⟨M, hM⟩
  have hpos : 0 < max M 0 + 1 := by positivity
  have := hM (trivS_hasMassGap R hpos)
  linarith [le_max_left M 0]

/-- … hence it violates the mass gap in the Clay sense. -/
theorem trivS_not_clayMassGap [Fintype ι] [NeZero d] (R : CompRep ι d) :
    ¬ ClayMassGap R (trivS ι d) := fun h => trivS_not_finiteMass R h.2

end ClayYM
