/-
ClayYM/OS.lean
==============
Euclidean quantum theory in the form of Schwinger KERNELS at non-coincident points,
and Osterwalder–Schrader axioms (OS 1973: E1–E4; OS 1975: linear growth condition E0').

Design choices (see STATEMENT.md, §3.1):
* The local gauge-invariant fields of YM₄ (canonical dimension ≥ 4 > d/2) are not random
  distributions (even `:φ²:` of the free field in dimension 4 has infinite variance):
  the framework "probability measure on S'(ℝ⁴)" (Glimm–Jaffe OS0–OS4) does not suit them.
  We therefore use the Schwinger functions of OS 1973, defined off the diagonals.
* For a reconstructible theory, these functions are real analytic off the diagonals;
  we handle them as functions (kernels) `S : list of (index, point) → ℝ`. The values at
  coincident points are arbitrary and enter no axiom.
* The fields have components (indices `ι`) on which `O(d)` acts through a given matrix
  representation `R` (for Yang–Mills: the rank-4 tensor representation).
-/
import ClayYM.Basic

open scoped ContDiff BigOperators
open MeasureTheory Filter Topology

noncomputable section

namespace ClayYM

variable {ι : Type} {d : ℕ}

/-- Schwinger functions in kernel form: `S [(i₁,x₁), …, (iₙ,xₙ)]`. -/
abbrev Schwinger (ι : Type) (d : ℕ) : Type := LList ι d → ℝ

/-- Matrix representation of `O(d)` on the field components. -/
abbrev CompRep (ι : Type) (d : ℕ) : Type := Orth d → Matrix ι ι ℝ

/-! ### Reflection-positivity form -/

/-- Kernel of the reflection form between two terms `a` (reflected) and `b` (translated by `t`
in time): `Σ_j Π_k R(θ)_{i_{n-1-k}, j_k} · S((j, θ x_rev) ++ (labels_b, y + t e₀))`.
This is `S_{n+m}(Θ f* ⊗ τ_t g)` of OS 1973 written with kernels (Θf*(x₁…xₙ) = f(θxₙ,…,θx₁), real
functions), with the action of `θ` on the tensor components. -/
def rpKernel [Fintype ι] [NeZero d] (R : CompRep ι d) (S : Schwinger ι d) (a b : Term ι d)
    (t : ℝ) (x : Config d a.n) (y : Config d b.n) : ℝ :=
  ∑ j : Fin a.n → ι, (∏ k, R (θ d) (a.labels (Fin.rev k)) (j k)) *
    S (mkList j (fun k => θ d (x (Fin.rev k))) ++ mkList b.labels (fun k => y k + t • e₀ d))

/-- The Osterwalder–Schrader bilinear form `⟪F, τ_t G⟫ = Σ_{a∈F} Σ_{b∈G} ∫∫ f_a(x) g_b(y) K(x,y)`.
For `t = 0` it is the (pre-Hilbert) inner product of the reconstruction; `τ_t` acts there
as `e^{-tH}`. -/
def rpForm [Fintype ι] [NeZero d] (R : CompRep ι d) (S : Schwinger ι d)
    (F G : Family ι d) (t : ℝ) : ℝ :=
  (F.map fun a => (G.map fun b =>
      ∫ x, ∫ y, a.f x * b.f y * rpKernel R S a b t x y).sum).sum

/-! ### Osterwalder–Schrader axioms (kernel form) -/

/-- The Osterwalder–Schrader axioms for real Schwinger kernels:
* `normalized`            : `S(∅) = 1` (normalised vacuum);
* `smooth`                : E0 — `C^∞` regularity off the diagonals;
* `linear_growth`         : E0' (OS 1975) in the form of a sufficient pointwise bound, of order
                            linear in `n` and with at most factorial constants;
* `translation_invariant`, `rotation_covariant` : E1 — Euclidean covariance under the FULL
                            group `ℝ^d ⋊ O(d)` (reflections included);
* `symmetric`             : E3 — symmetry under permutations (Bose statistics, locality);
* `reflection_positive`   : E2 — reflection positivity;
* `cluster`               : E4 — cluster property (factorisation at large separation). -/
structure OSAxioms [Fintype ι] [NeZero d] (R : CompRep ι d) (S : Schwinger ι d) : Prop where
  normalized : S [] = 1
  smooth : ∀ (n : ℕ) (i : Fin n → ι),
    ContDiffOn ℝ ∞ (fun x : Config d n => S (mkList i x)) {x | NonCoincident x}
  linear_growth : ∃ α β c : ℝ, 0 < α ∧ 0 ≤ β ∧ 0 ≤ c ∧
    ∀ (n : ℕ) (i : Fin n → ι) (x : Config d n), NonCoincident x →
      |S (mkList i x)| ≤
        α * (n.factorial : ℝ) ^ β * ((1 + ∑ k, ‖x k‖) * (1 + (minDist x)⁻¹)) ^ (c * n)
  translation_invariant : ∀ (a : Spacetime d) (l : LList ι d), NonCoinc l →
    S (shiftList a l) = S l
  rotation_covariant : ∀ (g : Orth d) (n : ℕ) (i : Fin n → ι) (x : Config d n),
    NonCoincident x →
      S (mkList i (fun k => g (x k))) = ∑ j : Fin n → ι, (∏ k, R g (i k) (j k)) * S (mkList j x)
  symmetric : ∀ l l' : LList ι d, l.Perm l' → S l = S l'
  reflection_positive : ∀ F : Family ι d, 0 ≤ rpForm R S F F 0
  cluster : ∀ (l l' : LList ι d) (a : Spacetime d), NonCoinc l → NonCoinc l' →
    time a = 0 → a ≠ 0 →
      Tendsto (fun s : ℝ => S (l ++ shiftList (s • a) l')) atTop (𝓝 (S l * S l'))

end ClayYM
