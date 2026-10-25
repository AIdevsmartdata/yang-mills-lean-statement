/-
ClayYM/Fake/YM2D.lean
=====================
FAKE MODEL: Yang–Mills in dimension 2 (on the plane).

1. Exclusion by TYPE: the statements `ClayYM_A`, `ClayYM_B`, `ClayYM_AB` are about kernels
   `Schwinger YMIdx 4` (space-time `EuclideanSpace ℝ (Fin 4)`, tensor indices in `Fin 4`,
   torus `(ℤ/(L+1)ℤ)⁴`, transformations of `O(4)`): a two-dimensional theory is not an
   object of the right type. Nothing is left to the witness's choice (unlike the "arbitrary
   Poincaré group" of the lean-dojo sketch).
2. Exclusion by CONTENT, in the part that is generic in `d` (OS axioms + gap + `m < ∞`):
   in dimension 2, the YM curvature is a white noise (axial gauge); the gauge-invariant local
   fields at SEPARATED points are independent, so all their connected Schwinger functions
   vanish: the local sector is the trivial theory (a mathematical fact cited in STATEMENT.md,
   not formalised here). But the trivial theory in dimension 2 violates
   `m < ∞` (proved below, for every representation of `O(2)` on the components).
-/
import ClayYM.Fake.Trivial

namespace ClayYM

/-- The (trivial) local sector of YM₂ violates "m < ∞". -/
theorem ym2d_local_sector_not_finiteMass (ι : Type) [Fintype ι] (R : CompRep ι 2) :
    ¬ FiniteMass R (trivS ι 2) :=
  trivS_not_finiteMass R

/-- … although it satisfies all the Osterwalder–Schrader axioms in dimension 2. -/
theorem ym2d_local_sector_OS (ι : Type) [Fintype ι] (R : CompRep ι 2) :
    OSAxioms R (trivS ι 2) :=
  trivS_OSAxioms R

end ClayYM
