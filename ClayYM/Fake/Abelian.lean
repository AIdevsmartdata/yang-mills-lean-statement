/-
ClayYM/Fake/Abelian.lean
========================
FAKE MODEL: Maxwell theory (group `U(1)`), and more generally every group that admits a faithful
unitary representation of dimension `N ≤ 1`. In 4D, Maxwell theory is free and has no mass gap
(massless photon): if `U(1)` were admitted among the "compact simple groups", the universal
statement `∀ G` would become FALSE. Proved guard: a Lie algebra of `N × N` matrices with
`N ≤ 1` is commutative, hence never simple; no `CompactSimpleGroup` has `N ≤ 1`.
(Tori, `U(2)`, `SU(2)×SU(2)` are excluded by the same simplicity clause — not formalised here.)
-/
import ClayYM.Group

namespace ClayYM

/-- `1 × 1` matrices commute: no subset of `M₁(ℂ)` is a simple Lie algebra. -/
theorem not_simple_dim_one (𝔤 : Set (Matrix (Fin 1) (Fin 1) ℂ)) : ¬ IsSimpleLieAlg 𝔤 := by
  rintro ⟨⟨X, -, Y, -, hXY⟩, -⟩
  apply hXY
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, mul_comm]

/-- `0 × 0` matrices commute (degenerate case). -/
theorem not_simple_dim_zero (𝔤 : Set (Matrix (Fin 0) (Fin 0) ℂ)) : ¬ IsSimpleLieAlg 𝔤 := by
  rintro ⟨⟨X, -, Y, -, hXY⟩, -⟩
  exact hXY (Subsingleton.elim _ _)

/-- A simple Lie algebra of `N × N` matrices forces `N ≥ 2`. -/
theorem two_le_of_simple {N : ℕ} {𝔤 : Set (Matrix (Fin N) (Fin N) ℂ)} (h : IsSimpleLieAlg 𝔤) :
    2 ≤ N := by
  by_contra hN
  push_neg at hN
  interval_cases N
  · exact not_simple_dim_zero _ h
  · exact not_simple_dim_one _ h

/-- No compact simple group is presented by a representation of dimension `≤ 1`:
in particular `U(1)` (and every subgroup of `U(1)`) is excluded. -/
theorem CompactSimpleGroup.two_le_N (K : CompactSimpleGroup) : 2 ≤ K.N :=
  two_le_of_simple K.simple

end ClayYM
