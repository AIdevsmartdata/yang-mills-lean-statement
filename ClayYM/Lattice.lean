/-
ClayYM/Lattice.lean
===================
Wilson approximation (Jaffe–Witten §6.5):
"Wilson suggested a different approach based on approximating continuum space-time by a lattice, on
which he defined a gauge-invariant action. With a compact gauge group and a compactified space-time,
the lattice approximation reduces the functional integration to a finite-dimensional integral. One
must then verify the existence of limits of appropriate expectations of gauge-invariant observables
as the lattice spacing tends to zero and as the volume tends to infinity."

Concrete definitions (no hypothesis):
* torus `Λ_L = (ℤ/(L+1)ℤ)⁴`, links `(x, μ)`, configurations `U : links → G`;
* product of the normalised Haar measures;
* Wilson action `S_β(U) = β Σ_x Σ_{μ<ν} (1 − Re tr ρ(U_p)/N)`;
* Gibbs expectation `⟨O⟩_{L,β} = ∫ O e^{−S} dHaar / ∫ e^{−S} dHaar`;
* plaquette estimator `Q_{μνρσ}(x) = −Re tr(P_{μν}(x) P_{ρσ}(x)) / a⁴`, `P = (U_p − U_p†)/2`
  (for smooth `U = exp(a A)`, `P_{μν} = a² F_{μν} + O(a³)`);
* renormalised fields `Φ_α = Σ_γ Z_{αγ} Q_γ − c_α` (mixing of the 21 components and subtraction
  of the identity), correlations smeared with test functions (Riemann sums on the lattice);
* continuous gauge-invariant local observables (box of radius `r`).
-/
import ClayYM.Fingerprint

open scoped BigOperators
open MeasureTheory Filter Topology

noncomputable section

namespace ClayYM

/-- Sites of the torus `(ℤ/(L+1)ℤ)⁴` (side `L+1 ≥ 1`). -/
abbrev Site (L : ℕ) : Type := Fin 4 → ZMod (L + 1)

/-- Oriented links `(x, μ)` from the site `x` to `x + e_μ`. -/
abbrev Link (L : ℕ) : Type := Site L × Fin 4

/-- Gauge configurations on the torus. -/
abbrev LinkConfig (G : Type) (L : ℕ) : Type := Link L → G

section HaarAndAction

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- Normalised Haar measure (`μ(G) = 1`). -/
def haarProb : Measure G := Measure.haarMeasure ⊤

/-- Product measure ("Haar on every link") on the configurations. -/
def linkMeasure (L : ℕ) : Measure (LinkConfig G L) :=
  Measure.pi (fun _ : Link L => haarProb G)

end HaarAndAction

/-- Neighbouring site `x + e_μ`. -/
def stepSite {L : ℕ} (x : Site L) (μ : Fin 4) : Site L := x + Pi.single μ 1

/-- Plaquette element `U_p(x;μ,ν) = U(x,μ) U(x+μ,ν) U(x+ν,μ)⁻¹ U(x,ν)⁻¹`. -/
def plaqG {G : Type} [Group G] {L : ℕ} (U : LinkConfig G L) (x : Site L) (μ ν : Fin 4) : G :=
  U (x, μ) * U (stepSite x μ, ν) * (U (stepSite x ν, μ))⁻¹ * (U (x, ν))⁻¹

section Wilson

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] {N : ℕ}
  (ρ : G →* Matrix.unitaryGroup (Fin N) ℂ)

/-- Unitary matrix of the plaquette in the representation `ρ` (the one of the Wilson action). -/
def plaqM {L : ℕ} (U : LinkConfig G L) (x : Site L) (μ ν : Fin 4) :
    Matrix (Fin N) (Fin N) ℂ :=
  ((ρ (plaqG U x μ ν) : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)

/-- Wilson action `S_β(U) = β Σ_x Σ_{μ<ν} (1 − Re tr ρ(U_p) / N)`. -/
def wilsonAction (L : ℕ) (β : ℝ) (U : LinkConfig G L) : ℝ :=
  β * ∑ x : Site L, ∑ μ : Fin 4, ∑ ν : Fin 4,
    if μ < ν then 1 - (Matrix.trace (plaqM ρ U x μ ν)).re / N else 0

/-- Gibbs expectation `⟨O⟩_{L,β}`. -/
def latticeExpect (L : ℕ) (β : ℝ) (O : LinkConfig G L → ℝ) : ℝ :=
  (∫ U, O U * Real.exp (-wilsonAction ρ L β U) ∂linkMeasure G L) /
    (∫ U, Real.exp (-wilsonAction ρ L β U) ∂linkMeasure G L)

/-- Anti-Hermitian part of the plaquette `P_{μν} = (U_p − U_p†)/2`. -/
def plaqP {L : ℕ} (U : LinkConfig G L) (x : Site L) (μ ν : Fin 4) :
    Matrix (Fin N) (Fin N) ℂ :=
  (1 / 2 : ℂ) • (plaqM ρ U x μ ν - (plaqM ρ U x μ ν).conjTranspose)

/-- Lattice estimator of `Tr F_{μν} F_{ρσ}(x)` (spacing `a`): `−Re tr(P_{μν} P_{ρσ}) / a⁴`. -/
def plaqObs {L : ℕ} (a : ℝ) (U : LinkConfig G L) (x : Site L) (α : YMIdx) : ℝ :=
  -(Matrix.trace (plaqP ρ U x α.1 α.2.1 * plaqP ρ U x α.2.2.1 α.2.2.2)).re / a ^ 4

/-- Physical position of a site: `a · (representatives in ]−(L+1)/2, (L+1)/2])`. -/
def sitePos {L : ℕ} (a : ℝ) (x : Site L) : Spacetime 4 :=
  WithLp.toLp 2 (fun μ => a * ((x μ).valMinAbs : ℝ))

/-- Renormalised field `Φ_α(x) = Σ_γ Z_{αγ} Q_γ(x) − c_α`. -/
def renField {L : ℕ} (a : ℝ) (Z : Matrix YMIdx YMIdx ℝ) (c : YMIdx → ℝ)
    (U : LinkConfig G L) (x : Site L) (α : YMIdx) : ℝ :=
  ∑ γ, Z α γ * plaqObs ρ a U x γ - c α

/-- Generic smeared correlation: `a^{4n} Σ_{y} f(a y) ⟨Π_k φ(y_k, i_k)⟩_{L,β}`
for a family of lattice fields `φ : configuration → site → label → ℝ`. -/
def latSmeared {α : Type} (L : ℕ) (a β : ℝ) (φ : LinkConfig G L → Site L → α → ℝ)
    (n : ℕ) (i : Fin n → α) (f : Config 4 n → ℝ) : ℝ :=
  a ^ (4 * n) * ∑ y : Fin n → Site L,
    f (fun k => sitePos a (y k)) * latticeExpect ρ L β (fun U => ∏ k, φ U (y k) (i k))

end Wilson

/-- Sequence of lattices: `a_k → 0`, physical volume `(L_k+1) a_k → ∞`, weak coupling `β_k → ∞`. -/
structure LatticeSeq where
  a : ℕ → ℝ
  L : ℕ → ℕ
  β : ℕ → ℝ
  a_pos : ∀ k, 0 < a k
  a_lim : Tendsto a atTop (𝓝 0)
  vol_lim : Tendsto (fun k => ((L k : ℝ) + 1) * a k) atTop atTop
  β_lim : Tendsto β atTop atTop

/-- Admissible test functions for the convergence: continuous, compactly supported,
with support in the region of non-coincident configurations. -/
def AdmissibleTest {n : ℕ} (f : Config 4 n → ℝ) : Prop :=
  Continuous f ∧ HasCompactSupport f ∧ tsupport f ⊆ {x | NonCoincident x}

/-- Convergence of the smeared correlations (for `n ≥ 1`; `S(∅) = 1` is the normalisation axiom)
to the Schwinger kernels `S`: `lim_k latSmeared_k(f) = ∫ f(x) S(i; x) dx`. -/
def LatticeConverges {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {N : ℕ}
    (ρ : G →* Matrix.unitaryGroup (Fin N) ℂ) {α : Type} (sq : LatticeSeq)
    (φ : (k : ℕ) → LinkConfig G (sq.L k) → Site (sq.L k) → α → ℝ) (S : Schwinger α 4) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (i : Fin n → α) (f : Config 4 n → ℝ), AdmissibleTest f →
    Tendsto (fun k => latSmeared ρ (sq.L k) (sq.a k) (sq.β k) (φ k) n i f) atTop
      (𝓝 (∫ x, f x * S (mkList i x)))

/-! ### Gauge-invariant local observables -/

/-- Indices of the box of radius `r` around a site. -/
abbrev BoxIdx (r : ℕ) : Type := Fin 4 → Fin (2 * r + 1)

/-- Integer offset `b_ν − r ∈ [−r, r]`. -/
def boxOffset {r : ℕ} (b : BoxIdx r) : Fin 4 → ℤ := fun ν => (b ν : ℤ) - r

/-- Site `y + v` for an integer offset `v`. -/
def addInt {L : ℕ} (y : Site L) (v : Fin 4 → ℤ) : Site L := fun μ => y μ + (v μ : ZMod (L + 1))

/-- Local observable of radius `r`: a function of the variables of the links starting in the box. -/
abbrev LocalObs (G : Type) (r : ℕ) : Type := (BoxIdx r × Fin 4 → G) → ℝ

/-- Restriction of a configuration to the box centred at `y`. -/
def placeAt {G : Type} {r L : ℕ} (U : LinkConfig G L) (y : Site L) : BoxIdx r × Fin 4 → G :=
  fun p => U (addInt y (boxOffset p.1), p.2)

/-- Lattice gauge transformation `U(x,μ) ↦ h(x) U(x,μ) h(x+μ)⁻¹`. -/
def gaugeTransform {G : Type} [Group G] {L : ℕ} (h : Site L → G) (U : LinkConfig G L) :
    LinkConfig G L :=
  fun p => h p.1 * U p * (h (stepSite p.1 p.2))⁻¹

/-- Continuous gauge-invariant local observable (on every torus). -/
def GaugeInvariantLocal {G : Type} [Group G] [TopologicalSpace G] {r : ℕ} (O : LocalObs G r) :
    Prop :=
  Continuous O ∧ ∀ (L : ℕ) (h : Site L → G) (U : LinkConfig G L) (y : Site L),
    O (placeAt (gaugeTransform h U) y) = O (placeAt U y)

/-- Representation on the joint labels "Tr FF ⊕ even scalar observables":
tensor representation on the former, trivial on the latter. -/
def jointRep (m : ℕ) : CompRep (YMIdx ⊕ Fin m) 4 := fun g =>
  Matrix.fromBlocks (tensorRep4 g) 0 0 1

/-- Joint fields at step `k`: renormalised plaquette components, and renormalised local
observables `Σ_q Z'_{pq} O_q(y) − c'_p`. -/
def jointField {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] {N : ℕ}
    (ρ : G →* Matrix.unitaryGroup (Fin N) ℂ) {r m : ℕ} (O : Fin m → LocalObs G r) (L : ℕ) (a : ℝ)
    (Z : Matrix YMIdx YMIdx ℝ) (c : YMIdx → ℝ) (Z' : Matrix (Fin m) (Fin m) ℝ) (c' : Fin m → ℝ)
    (U : LinkConfig G L) (y : Site L) : YMIdx ⊕ Fin m → ℝ
  | Sum.inl α => renField ρ a Z c U y α
  | Sum.inr p => ∑ q, Z' p q * O q (placeAt U y) - c' p

end ClayYM
