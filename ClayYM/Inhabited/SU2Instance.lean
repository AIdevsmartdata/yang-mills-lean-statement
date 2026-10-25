/-
ClayYM/Inhabited/SU2Instance.lean
=================================
**Non-vacuity of the quantifier "for every compact simple group G"**: the class
`CompactSimpleGroup` is inhabited by SU(2) (`compactSimpleGroup_nonempty`). The statements
`ClayYM_A`, `ClayYM_B`, `ClayYM_AB` (of the form `∀ K : CompactSimpleGroup, …`) are therefore not
vacuously true (the lesson of the lean-dojo Hodge statement, vacuously true because its varieties
had no points). Additional check: `dim SU(2) = 3` for the definition `CompactSimpleGroup.dim`
used in the fingerprint FP3.
-/
import ClayYM.Inhabited.SU2Exp

open Matrix

noncomputable section

namespace ClayYM

namespace SU2

instance instSecondCountableMatrix : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))

instance instSecondCountableG : SecondCountableTopology G :=
  TopologicalSpace.Subtype.secondCountableTopology _

instance instMeasurableSpace : MeasurableSpace G := borel G

instance instBorelSpace : BorelSpace G := ⟨rfl⟩

/-- SU(2), presented by its inclusion into U(2), as a compact simple gauge group. -/
def compactSimpleGroup : CompactSimpleGroup where
  G := G
  N := 2
  ρ := ρ
  ρ_continuous := ρ_continuous
  ρ_injective := ρ_injective
  simple := simple

/-- `e₁, e₂, e₃` are `ℝ`-linearly independent. -/
lemma linearIndependent_e : LinearIndependent ℝ ![e1, e2, e3] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h00 := congrFun (congrFun hg 0) 0
  have h01 := congrFun (congrFun hg 0) 1
  simp [Fin.sum_univ_three, e1, e2, e3, Complex.ext_iff] at h00 h01
  intro i
  fin_cases i
  · simpa using h00
  · simpa using h01.1
  · simpa using h01.2

lemma span_su2 : Submodule.span ℝ su2 = Submodule.span ℝ (Set.range ![e1, e2, e3]) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro X hX
    rw [eq_comb hX]
    have h1 : e1 ∈ Submodule.span ℝ (Set.range ![e1, e2, e3]) :=
      Submodule.subset_span ⟨0, rfl⟩
    have h2 : e2 ∈ Submodule.span ℝ (Set.range ![e1, e2, e3]) :=
      Submodule.subset_span ⟨1, rfl⟩
    have h3 : e3 ∈ Submodule.span ℝ (Set.range ![e1, e2, e3]) :=
      Submodule.subset_span ⟨2, rfl⟩
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ h1)
      (Submodule.smul_mem _ _ h2)) (Submodule.smul_mem _ _ h3)
  · apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact e1_mem
    · exact e2_mem
    · exact e3_mem

/-- `dim SU(2) = 3`. -/
theorem dim_eq_three : compactSimpleGroup.dim = 3 := by
  have hdef : compactSimpleGroup.dim = Module.finrank ℝ (Submodule.span ℝ (lieAlgebraOf ρ)) := rfl
  rw [hdef, lieAlgebra_eq, span_su2, finrank_span_eq_card linearIndependent_e]
  simp

end SU2

/-- **The class of compact simple groups is not empty** (it contains SU(2)). -/
theorem compactSimpleGroup_nonempty : Nonempty CompactSimpleGroup :=
  ⟨SU2.compactSimpleGroup⟩

end ClayYM
