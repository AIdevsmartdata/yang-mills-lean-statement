/-
ClayYM/Basic.lean
=================
Basic geometric objects for the Euclidean (Osterwalder–Schrader) statement:
Euclidean space-time `ℝ^d`, orthogonal group `O(d)`, time reflection `θ`,
configurations of `n` points, test functions with ordered positive times (the space `°S₊`
of Osterwalder–Schrader 1973), families of test functions (vectors of the pre-Hilbert space
of the OS reconstruction).

No hypothesis, no axiom, no `sorry` in this file: only concrete definitions built from
Mathlib.
-/
import Mathlib

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace ClayYM

/-- Euclidean space-time `ℝ^d` (Mathlib's ℓ² norm and inner product). -/
abbrev Spacetime (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- The orthogonal group `O(d)`: bijective linear isometries of `ℝ^d`
(rotations AND reflections: the full group, not only `SO(d)`). -/
abbrev Orth (d : ℕ) : Type := Spacetime d ≃ₗᵢ[ℝ] Spacetime d

variable {d : ℕ}

/-- Euclidean time coordinate: the coordinate with index `0`. -/
def time [NeZero d] (x : Spacetime d) : ℝ := x 0

/-- Unit vector of the time direction. -/
def e₀ (d : ℕ) [NeZero d] : Spacetime d := EuclideanSpace.single 0 1

/-! ### Time reflection -/

/-- Sign of the time reflection on coordinate `i`: `-1` for time, `+1` otherwise. -/
def θsign [NeZero d] (i : Fin d) : ℝ := if i = 0 then -1 else 1

lemma θsign_mul_self [NeZero d] (i : Fin d) : θsign i * θsign i = 1 := by
  unfold θsign; split_ifs <;> norm_num

/-- Time reflection as the linear map `(t, x⃗) ↦ (-t, x⃗)`. -/
def θlin [NeZero d] : Spacetime d →ₗ[ℝ] Spacetime d where
  toFun x := WithLp.toLp 2 (fun i => θsign i * x i)
  map_add' x y := by
    ext i; simp [mul_add]
  map_smul' c x := by
    ext i; simp; ring

lemma θlin_apply [NeZero d] (x : Spacetime d) (i : Fin d) : θlin x i = θsign i * x i := rfl

lemma θlin_θlin [NeZero d] (x : Spacetime d) : θlin (θlin x) = x := by
  ext i; simp only [θlin_apply, ← mul_assoc, θsign_mul_self, one_mul]

lemma norm_θlin [NeZero d] (x : Spacetime d) : ‖θlin x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [θlin_apply, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, mul_pow]
  have : θsign i ^ 2 = 1 := by rw [sq]; exact θsign_mul_self i
  rw [this, one_mul]

/-- The time reflection `θ ∈ O(d)`. -/
def θ (d : ℕ) [NeZero d] : Orth d where
  toLinearEquiv :=
    { θlin with
      invFun := θlin
      left_inv := fun x => θlin_θlin x
      right_inv := fun x => θlin_θlin x }
  norm_map' := norm_θlin

lemma θ_apply [NeZero d] (x : Spacetime d) (i : Fin d) : θ d x i = θsign i * x i := rfl

lemma time_θ [NeZero d] (x : Spacetime d) : time (θ d x) = - time x := by
  simp [time, θ_apply, θsign]

/-! ### Configurations -/

/-- Configurations of `n` points of `ℝ^d`. -/
abbrev Config (d n : ℕ) : Type := Fin n → Spacetime d

/-- The `n` points are pairwise distinct (non-coincident configuration). -/
def NonCoincident {n : ℕ} (x : Config d n) : Prop := Function.Injective x

/-- Smallest distance between two distinct points (distinct indices) of a configuration;
equals `0` (Mathlib's convention `sInf ∅ = 0`) if `n ≤ 1`. -/
def minDist {n : ℕ} (x : Config d n) : ℝ :=
  ⨅ p : {p : Fin n × Fin n // p.1 ≠ p.2}, dist (x p.1.1) (x p.1.2)

/-- Region of strictly positive, strictly ordered times: `0 < t₁ < t₂ < … < tₙ`. -/
def OrderedPositive [NeZero d] (n : ℕ) : Set (Config d n) :=
  {x | (∀ k, 0 < time (x k)) ∧ StrictMono (fun k => time (x k))}

/-- Test functions of `°S₊`: smooth (`C^∞`, as opposed to analytic: we fix `∞ = ((⊤ : ℕ∞) : ℕ∞ω)`),
with compact support contained in the region of ordered positive times. -/
structure PosTest (d n : ℕ) [NeZero d] where
  toFun : Config d n → ℝ
  smooth : ContDiff ℝ ∞ toFun
  compact : HasCompactSupport toFun
  supp : tsupport toFun ⊆ OrderedPositive n

instance [NeZero d] {n : ℕ} : CoeFun (PosTest d n) (fun _ => Config d n → ℝ) :=
  ⟨PosTest.toFun⟩

/-! ### Lists of labelled points -/

/-- List of labelled points `(field index, point)`, the argument of the Schwinger functions. -/
abbrev LList (ι : Type) (d : ℕ) : Type := List (ι × Spacetime d)

/-- The list `[(i₀, x₀), …, (iₙ₋₁, xₙ₋₁)]`. -/
def mkList {ι : Type} {n : ℕ} (i : Fin n → ι) (x : Config d n) : LList ι d :=
  List.ofFn (fun k => (i k, x k))

/-- Pairwise distinct points in a labelled list. -/
def NonCoinc {ι : Type} (l : LList ι d) : Prop := (l.map Prod.snd).Nodup

/-- Translation of a labelled list by a vector `a`. -/
def shiftList {ι : Type} (a : Spacetime d) (l : LList ι d) : LList ι d :=
  l.map (fun p => (p.1, p.2 + a))

/-! ### Families of test functions (vectors of the OS reconstruction) -/

/-- A term `f(x₁,…,xₙ)` carrying the field indices `labels`. -/
structure Term (ι : Type) (d : ℕ) [NeZero d] where
  n : ℕ
  labels : Fin n → ι
  f : PosTest d n

/-- A finite family of terms (the finite sequence `(f₀, f₁, …)` of Osterwalder–Schrader). -/
abbrev Family (ι : Type) (d : ℕ) [NeZero d] : Type := List (Term ι d)

/-- The constant function `1` on the one-point space `Config d 0`: the vacuum vector. -/
def vacTest [NeZero d] : PosTest d 0 where
  toFun := fun _ => 1
  smooth := contDiff_const
  compact := by
    have : CompactSpace (Config d 0) := Finite.compactSpace
    exact HasCompactSupport.of_compactSpace _
  supp := by
    intro x _
    refine ⟨fun k => k.elim0, fun a _ _ => a.elim0⟩

/-- The vacuum term (no point, function `1`). -/
def vacTerm (ι : Type) [NeZero d] : Term ι d := ⟨0, Fin.elim0, vacTest⟩

/-- The vacuum family `Ω = (1, 0, 0, …)`. -/
def vac (ι : Type) [NeZero d] : Family ι d := [vacTerm ι]

end ClayYM
