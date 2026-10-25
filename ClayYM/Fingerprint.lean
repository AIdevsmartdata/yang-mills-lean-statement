/-
ClayYM/Fingerprint.lean
=======================
Yang–Mills "fingerprint" for the axiomatic variant (B).

Jaffe–Witten §4: "one should define a quantum field theory … with local quantum field operators in
correspondence with the gauge-invariant local polynomials in the curvature F and its covariant
derivatives, such as Tr F_ij F_kl(x). Correlation functions of the quantum field operators should
agree at short distances with the predictions of asymptotic freedom and perturbative renormalization
theory, as described in textbooks. Those predictions include among other things the existence of a
stress tensor and an operator product expansion, having prescribed local singularities predicted by
asymptotic freedom."

This file encodes, for the operators of dimension 4:
* the composite field `Tr F_{μν} F_{ρσ}`: 256 indices `(μ,ν,ρ,σ)` subject to the symmetries
  (antisymmetry within each pair, symmetry under exchange of the pairs) — 21 independent components,
  rank-4 tensor representation of the FULL group O(4);
* a stress-energy tensor `T_{μν} = z₁ (Σ_ρ F_{μρ}F_{νρ} − ¼ δ_{μν} F²) + z₂ δ_{μν} F²`
  (a combination of the components, `z₁ ≠ 0`), CONSERVED at non-coincident points, and NORMALISED
  absolutely by the energy Ward identity: `∫_{ℝ³} T₀₀(0, x⃗) d³x` generates the Euclidean time
  translations of the OS reconstruction;
* the ultraviolet fingerprint of asymptotic freedom (constants checked by
  `constants/sympy_constantes.py`):
  FP1: `|x|⁸ ⟨θ(x) θ(0)⟩_c · (log|x|)² → κ = 3 dim G/π⁴` as `x → 0`, with `θ = T_μμ` (trace
       anomaly); the value of `κ` has been IMPOSED since the adversarial review;
  FP2: `(|x|⁸⟨θθ⟩_c (log|x|)²/κ − 1) · L / log L → −b₁/b₀² = −102/121`, `L = −log|x|`;
  FP3: `s⁸ ⟨T_{μν}(s u) T_{ρσ}(0)⟩_c → dim G · (4/π⁴) · ℐ_{μν,ρσ}(u)` for every unit vector `u`
       (`4/π⁴ = C_T` of the free Maxwell field, `ℐ` = Osborn–Petkou conformal structure);
* indecomposability: the theory is not a sum of two non-trivial decoupled sectors (without it,
  FP1–FP3 being additive, `YM_{G₁} ⊗ YM_{G₂}` would mimic a group of the summed dimension).
-/
import ClayYM.Gap
import ClayYM.Group

open scoped ContDiff BigOperators
open MeasureTheory Filter Topology

noncomputable section

namespace ClayYM

/-- Indices `(μ, ν, ρ, σ)` of the components of the composite field `Tr F_{μν} F_{ρσ}`. -/
abbrev YMIdx : Type := Fin 4 × Fin 4 × Fin 4 × Fin 4

/-- Matrix coefficient `g_{ij} = (g e_j)_i` of an element of `O(4)`. -/
def orthEntry (g : Orth 4) (i j : Fin 4) : ℝ := g (EuclideanSpace.single j 1) i

/-- Rank-4 tensor representation of `O(4)` on the components `(μ,ν,ρ,σ)`. -/
def tensorRep4 : CompRep YMIdx 4 := fun g a b =>
  orthEntry g a.1 b.1 * orthEntry g a.2.1 b.2.1 * orthEntry g a.2.2.1 b.2.2.1 *
    orthEntry g a.2.2.2 b.2.2.2

/-- Exchange `μ ↔ ν`. -/
def swapA (a : YMIdx) : YMIdx := (a.2.1, a.1, a.2.2.1, a.2.2.2)
/-- Exchange `ρ ↔ σ`. -/
def swapB (a : YMIdx) : YMIdx := (a.1, a.2.1, a.2.2.2, a.2.2.1)
/-- Exchange of the pairs `(μν) ↔ (ρσ)`. -/
def swapP (a : YMIdx) : YMIdx := (a.2.2.1, a.2.2.2, a.1, a.2.1)

/-- Symmetries of the tensor `Tr F_{μν}F_{ρσ}`, imposed as identities between Schwinger functions
(at non-coincident points): antisymmetry in `(μν)` and in `(ρσ)`, exchange symmetry. -/
def TensorSymmetric (S : Schwinger YMIdx 4) : Prop :=
  ∀ (n : ℕ) (i : Fin n → YMIdx) (x : Config 4 n) (k : Fin n), NonCoincident x →
    S (mkList (Function.update i k (swapA (i k))) x) = - S (mkList i x) ∧
    S (mkList (Function.update i k (swapB (i k))) x) = - S (mkList i x) ∧
    S (mkList (Function.update i k (swapP (i k))) x) = S (mkList i x)

/-! ### Linear combinations of components -/

/-- Coefficient vector over the components (a linear composite field). -/
abbrev Coef : Type := YMIdx → ℝ

/-- `S((c, x) :: rest) = Σ_a c_a S((a,x) :: rest)`. -/
def S1 (S : Schwinger YMIdx 4) (c : Coef) (x : Spacetime 4) (rest : LList YMIdx 4) : ℝ :=
  ∑ a, c a * S ((a, x) :: rest)

/-- Two-point function of two linear combinations. -/
def S2 (S : Schwinger YMIdx 4) (c c' : Coef) (x y : Spacetime 4) : ℝ :=
  ∑ a, ∑ b, c a * c' b * S [(a, x), (b, y)]

/-- CONNECTED two-point function (the vacuum is subtracted). -/
def conn2 (S : Schwinger YMIdx 4) (c c' : Coef) (x y : Spacetime 4) : ℝ :=
  S2 S c c' x y - S1 S c x [] * S1 S c' y []

/-- `δ_{μν}`. -/
def kd (μ ν : Fin 4) : ℝ := if μ = ν then 1 else 0

/-- `F² = Σ_{μν} F_{μν}F_{μν}`. -/
def Fsq : Coef := fun a => if a.1 = a.2.2.1 ∧ a.2.1 = a.2.2.2 then 1 else 0

/-- `Σ_ρ F_{μρ} F_{νρ}`. -/
def FF (μ ν : Fin 4) : Coef := fun a => if a.1 = μ ∧ a.2.2.1 = ν ∧ a.2.1 = a.2.2.2 then 1 else 0

/-- Candidate stress tensor `T_{μν}(z₁,z₂) = z₁ (FF_{μν} − ¼ δ_{μν} F²) + z₂ δ_{μν} F²`. -/
def Tc (z₁ z₂ : ℝ) (μ ν : Fin 4) : Coef := fun a =>
  z₁ * (FF μ ν a - (1 / 4) * kd μ ν * Fsq a) + z₂ * kd μ ν * Fsq a

/-- Trace anomaly `θ = Σ_μ T_{μμ}`. -/
def θc (z₁ z₂ : ℝ) : Coef := fun a => ∑ μ, Tc z₁ z₂ μ μ a

/-! ### Conservation and Ward normalisation -/

/-- `e_μ`. -/
def eμ (μ : Fin 4) : Spacetime 4 := EuclideanSpace.single μ 1

/-- Conservation `∂_μ T_{μν}(x) = 0` in every correlation, at non-coincident points. -/
def Conserved (S : Schwinger YMIdx 4) (z₁ z₂ : ℝ) : Prop :=
  ∀ (ν : Fin 4) (n : ℕ) (i : Fin n → YMIdx) (y : Config 4 n) (x : Spacetime 4),
    NonCoincident y → x ∉ Set.range y →
      ∑ μ, lineDeriv ℝ (fun x' => S1 S (Tc z₁ z₂ μ ν) x' (mkList i y)) x (eμ μ) = 0

/-- Point `(0, v⃗)` of the time-zero slice. -/
def slice (v : Fin 3 → ℝ) : Spacetime 4 := WithLp.toLp 2 (Fin.cons 0 v)

/-- Reflection kernel with the insertion of a linear field `c` (vacuum subtracted) at the point `p`. -/
def rpKernelIns (S : Schwinger YMIdx 4) (c : Coef) (p : Spacetime 4) (a b : Term YMIdx 4)
    (x : Config 4 a.n) (y : Config 4 b.n) : ℝ :=
  ∑ j : Fin a.n → YMIdx, (∏ k, tensorRep4 (θ 4) (a.labels (Fin.rev k)) (j k)) *
    (∑ e, c e * S (mkList j (fun k => θ 4 (x (Fin.rev k))) ++ (e, p) :: mkList b.labels y)
      - S1 S c p [] * S (mkList j (fun k => θ 4 (x (Fin.rev k))) ++ mkList b.labels y))

/-- `⟪F, T(c)(p) G⟫` (vacuum subtracted). -/
def rpFormIns (S : Schwinger YMIdx 4) (c : Coef) (p : Spacetime 4) (F G : Family YMIdx 4) : ℝ :=
  (F.map fun a => (G.map fun b =>
      ∫ x, ∫ y, a.f x * b.f y * rpKernelIns S c p a b x y).sum).sum

/-- Energy Ward identity: `d/dt ⟪F, τ_t G⟫|_{t=0} = ∫_{ℝ³} ⟪F, T₀₀(0,v⃗) G⟫ d³v`.
(Euclidean: `⟪F, τ_t G⟫ = ⟨F, e^{-tH} G⟩` and `H = −∫ T₀₀^E d³x` for the canonical Euclidean tensor;
the sign and the scale of `T` are absorbed by the existential choice of `z₁ ≠ 0`.) -/
def WardEnergy (S : Schwinger YMIdx 4) (z₁ z₂ : ℝ) : Prop :=
  ∀ F G : Family YMIdx 4,
    Integrable (fun v : Fin 3 → ℝ => rpFormIns S (Tc z₁ z₂ 0 0) (slice v) F G) ∧
    HasDerivAt (fun t => rpForm tensorRep4 S F G t)
      (∫ v : Fin 3 → ℝ, rpFormIns S (Tc z₁ z₂ 0 0) (slice v) F G) 0

/-! ### Ultraviolet fingerprint (asymptotic freedom) -/

/-- FP1 + FP2: `|x|⁸⟨θθ⟩_c (log|x|)² → κ` with the universal correction `−b₁/b₀² · log L / L`.
The value `κ` is imposed by `YMFingerprint` (see `traceAnomalyCoeff`). -/
def UVTrace (S : Schwinger YMIdx 4) (z₁ z₂ κ : ℝ) : Prop :=
  Tendsto (fun x : Spacetime 4 =>
      ‖x‖ ^ 8 * conn2 S (θc z₁ z₂) (θc z₁ z₂) x 0 * (Real.log ‖x‖) ^ 2)
    (𝓝[≠] 0) (𝓝 κ) ∧
  Tendsto (fun x : Spacetime 4 =>
      (‖x‖ ^ 8 * conn2 S (θc z₁ z₂) (θc z₁ z₂) x 0 * (Real.log ‖x‖) ^ 2 / κ - 1) *
        (-Real.log ‖x‖) / Real.log (-Real.log ‖x‖))
    (𝓝[≠] 0) (𝓝 (-(102 / 121)))

/-- Predicted value of `κ` for the Ward-normalised `θ`: `κ = dim G · c_{F²}/16 = 3 dim G/π⁴`
(`θ = (β(g)/2g) F^aF^a`, `ḡ² ≈ 8π²/(b₀ L)`: `b₀` cancels; `c_{F²} = 48/π⁴` per gluon,
checked by `constants/sympy_constantes.py`). Fixing `κ` rules out adding decoupled matter. -/
def traceAnomalyCoeff (K : CompactSimpleGroup) : ℝ := 3 * K.dim / Real.pi ^ 4

theorem traceAnomalyCoeff_pos (K : CompactSimpleGroup) : 0 < traceAnomalyCoeff K := by
  have h : (0 : ℝ) < K.dim := by exact_mod_cast K.dim_pos
  unfold traceAnomalyCoeff
  positivity

/-- `I_{μν}(u) = δ_{μν} − 2 u_μ u_ν` (inversion). -/
def invI (u : Spacetime 4) (μ ν : Fin 4) : ℝ := kd μ ν - 2 * u μ * u ν

/-- Conformal structure `ℐ_{μν,ρσ}(u) = ½(I_{μρ}I_{νσ} + I_{μσ}I_{νρ}) − ¼ δ_{μν}δ_{ρσ}`. -/
def confI (u : Spacetime 4) (μ ν ρ σ : Fin 4) : ℝ :=
  (1 / 2) * (invI u μ ρ * invI u ν σ + invI u μ σ * invI u ν ρ) - (1 / 4) * kd μ ν * kd ρ σ

/-- FP3: at short distance, `⟨T T⟩_c` is that of `dim G` free Maxwell fields. -/
def UVStress (K : CompactSimpleGroup) (S : Schwinger YMIdx 4) (z₁ z₂ : ℝ) : Prop :=
  ∀ u : Spacetime 4, ‖u‖ = 1 → ∀ μ ν ρ σ : Fin 4,
    Tendsto (fun s : ℝ => s ^ 8 * conn2 S (Tc z₁ z₂ μ ν) (Tc z₁ z₂ ρ σ) (s • u) 0)
      (𝓝[>] 0) (𝓝 ((K.dim : ℝ) * (4 / Real.pi ^ 4) * confI u μ ν ρ σ))

/-! ### Indecomposability (no decoupled sectors) -/

/-- Sublist selected by a Boolean mask. -/
def subList {α : Type} (l : List α) (s : Fin l.length → Bool) : List α :=
  ((List.finRange l.length).filter (fun k => s k)).map l.get

/-- Schwinger functions of the SUM of two independent fields (decoupled sectors):
`S(l) = Σ_{A ⊆ l} S₁(A) S₂(l ∖ A)`. -/
def indepSum (S₁ S₂ : Schwinger YMIdx 4) (l : LList YMIdx 4) : ℝ :=
  ∑ s : Fin l.length → Bool, S₁ (subList l s) * S₂ (subList l (fun k => !s k))

/-- The sector has a non-zero connected two-point function (it is neither trivial nor constant). -/
def HasConnected (S : Schwinger YMIdx 4) : Prop :=
  ∃ (c c' : Coef) (x : Spacetime 4), x ≠ 0 ∧ conn2 S c c' x 0 ≠ 0

/-- `S` is the theory of a sum of two decoupled sectors, each a non-trivial OS theory
(this is the case of the products `YM_{G₁} ⊗ YM_{G₂}`, or `YM_G ⊗ free matter`, which make the
ultraviolet data `κ` and `C_T` additive). -/
def Decomposable (S : Schwinger YMIdx 4) : Prop :=
  ∃ S₁ S₂ : Schwinger YMIdx 4, OSAxioms tensorRep4 S₁ ∧ OSAxioms tensorRep4 S₂ ∧
    HasConnected S₁ ∧ HasConnected S₂ ∧ ∀ l : LList YMIdx 4, NonCoinc l → S l = indepSum S₁ S₂ l

/-- Yang–Mills fingerprint for `G` (variant B, version strengthened after the adversarial review):
tensor symmetries; conserved, Ward-normalised stress tensor with FP1 (coefficient
`κ = 3 dim G/π⁴` IMPOSED), FP2, FP3; INDECOMPOSABLE theory. -/
structure YMFingerprint (K : CompactSimpleGroup) (S : Schwinger YMIdx 4) : Prop where
  tensor_symmetric : TensorSymmetric S
  stress_tensor : ∃ z₁ z₂ : ℝ, z₁ ≠ 0 ∧ Conserved S z₁ z₂ ∧ WardEnergy S z₁ z₂ ∧
    UVTrace S z₁ z₂ (traceAnomalyCoeff K) ∧ UVStress K S z₁ z₂
  indecomposable : ¬ Decomposable S

/-- `Σ_μ FF_{μμ} = F²`. -/
theorem sum_FF_diag (a : YMIdx) : ∑ μ, FF μ μ a = Fsq a := by
  obtain ⟨μ, ν, ρ, σ⟩ := a
  simp only [FF, Fsq, Fin.sum_univ_four]
  fin_cases μ <;> fin_cases ρ <;> simp

/-- Control computation: `θ = 4 z₂ F²` (the traceless part drops out). -/
theorem θc_eq (z₁ z₂ : ℝ) : θc z₁ z₂ = fun a => 4 * z₂ * Fsq a := by
  funext a
  have h := sum_FF_diag a
  rw [Fin.sum_univ_four] at h
  simp only [θc, Tc, kd, Fin.sum_univ_four, ↓reduceIte]
  linear_combination z₁ * h

end ClayYM
