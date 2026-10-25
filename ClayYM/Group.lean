/-
ClayYM/Group.lean
=================
"For any compact simple gauge group G" (Jaffe–Witten §4).

Encoding: `G` is a compact, Hausdorff, CONNECTED topological group with a continuous and FAITHFUL
unitary representation `ρ : G → U(N)` (every compact Lie group has one, by Peter–Weyl;
conversely, a compact group that has one is a closed subgroup of `U(N)`, hence a Lie group,
by Cartan's theorem). Its Lie algebra is defined concretely through the matrix exponential:
`𝔤_ρ = {X | ∀ t ∈ ℝ, exp(tX) ∈ ρ(G)}`, and "simple" means: `𝔤_ρ` is non-abelian and has
no ideal other than `0` and `𝔤_ρ`. This excludes: `U(1)` and tori (abelian), finite groups
(`𝔤 = 0`), products `SU(2) × SU(2)` (proper ideal), `U(2)` (one-dimensional centre).

Coefficients of the β function (pure YM, normalisation `β(g) = −b₀ g³/16π² − b₁ g⁵/(16π²)²`):
`b₀ = 11 C_A / 3`, `b₁ = 34 C_A² / 3` (C_A = h∨, long roots of squared length 2). We prove that
`b₁ / b₀² = 102/121` DOES NOT DEPEND on `G`: it is the only invariant of (b₀, b₁) visible in the
correlations of gauge-invariant operators normalised in a renormalisation-group-invariant way
(see Fingerprint.lean and STATEMENT.md).
-/
import ClayYM.Basic

open scoped BigOperators

noncomputable section

namespace ClayYM

/-- Real Lie algebra of the image of a unitary representation, defined through the exponential:
`𝔤_ρ = {X ∈ M_N(ℂ) | ∀ t : ℝ, exp(t • X) ∈ ρ(G)}`. -/
def lieAlgebraOf {G : Type} [Group G] {N : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin N) ℂ) :
    Set (Matrix (Fin N) (Fin N) ℂ) :=
  {X | ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈
      Set.range (fun g => ((ρ g : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ))}

/-- A subset `𝔤` of `M_N(ℂ)` is a SIMPLE Lie algebra (in the real sense): non-abelian,
and every real subspace `V ⊆ 𝔤` stable under `[𝔤, ·]` is `0` or `𝔤`. -/
def IsSimpleLieAlg {N : ℕ} (𝔤 : Set (Matrix (Fin N) (Fin N) ℂ)) : Prop :=
  (∃ X ∈ 𝔤, ∃ Y ∈ 𝔤, X * Y - Y * X ≠ 0) ∧
  ∀ V : Submodule ℝ (Matrix (Fin N) (Fin N) ℂ), (V : Set (Matrix (Fin N) (Fin N) ℂ)) ⊆ 𝔤 →
    (∀ X ∈ 𝔤, ∀ Y ∈ V, X * Y - Y * X ∈ V) →
      V = ⊥ ∨ (V : Set (Matrix (Fin N) (Fin N) ℂ)) = 𝔤

/-- A compact simple gauge group, presented with a faithful unitary representation. -/
structure CompactSimpleGroup where
  G : Type
  [instGroup : Group G]
  [instTop : TopologicalSpace G]
  [instTopGroup : IsTopologicalGroup G]
  [instCompact : CompactSpace G]
  [instT2 : T2Space G]
  [instConnected : ConnectedSpace G]
  [instMeas : MeasurableSpace G]
  [instBorel : BorelSpace G]
  [instSecond : SecondCountableTopology G]
  /-- dimension of the faithful representation -/
  N : ℕ
  /-- faithful unitary representation -/
  ρ : G →* Matrix.unitaryGroup (Fin N) ℂ
  ρ_continuous : Continuous ρ
  ρ_injective : Function.Injective ρ
  /-- the Lie algebra is simple -/
  simple : IsSimpleLieAlg (lieAlgebraOf ρ)

attribute [instance] CompactSimpleGroup.instGroup CompactSimpleGroup.instTop
  CompactSimpleGroup.instTopGroup CompactSimpleGroup.instCompact CompactSimpleGroup.instT2
  CompactSimpleGroup.instConnected CompactSimpleGroup.instMeas CompactSimpleGroup.instBorel
  CompactSimpleGroup.instSecond

/-- `dim G`: real dimension of the Lie algebra. -/
def CompactSimpleGroup.dim (K : CompactSimpleGroup) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ (lieAlgebraOf K.ρ))

/-- `dim G > 0` (a simple Lie algebra is non-zero). -/
theorem CompactSimpleGroup.dim_pos (K : CompactSimpleGroup) : 0 < K.dim := by
  obtain ⟨⟨X, hX, Y, -, hXY⟩, -⟩ := K.simple
  have hX0 : X ≠ 0 := by
    rintro rfl
    simp at hXY
  unfold CompactSimpleGroup.dim
  rw [Module.finrank_pos_iff_exists_ne_zero]
  refine ⟨⟨X, Submodule.subset_span hX⟩, ?_⟩
  intro h
  apply hX0
  simpa using congrArg Subtype.val h

/-! ### Coefficients of the β function of pure Yang–Mills -/

/-- `b₀ = 11 C_A / 3`. -/
def b0 (CA : ℝ) : ℝ := 11 / 3 * CA

/-- `b₁ = 34 C_A² / 3`. -/
def b1 (CA : ℝ) : ℝ := 34 / 3 * CA ^ 2

/-- Universality: `b₁ / b₀² = 102/121` for every group (every `C_A ≠ 0`). -/
theorem b1_div_b0_sq (CA : ℝ) (h : CA ≠ 0) : b1 CA / (b0 CA) ^ 2 = 102 / 121 := by
  unfold b0 b1
  field_simp
  ring

end ClayYM
