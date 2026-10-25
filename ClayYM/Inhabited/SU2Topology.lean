/-
ClayYM/Inhabited/SU2Topology.lean
=================================
The group `SU(2) = Matrix.specialUnitaryGroup (Fin 2) ℂ` (submonoid of `M₂(ℂ)`, induced topology):
topological group, compact (closed and bounded), connected (continuous image of the sphere `S³ ⊂ ℝ⁴`
under `(a, b) ↦ [[a, −b̄], [b, ā]]`), and the continuous injective inclusion `SU(2) → U(2)`.
-/
import ClayYM.Inhabited.SU2Algebra

open Matrix Topology

noncomputable section

namespace ClayYM

namespace SU2

/-- The type `SU(2)`. -/
abbrev G : Type := ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)

instance : ContinuousInv G where
  continuous_inv := by
    apply continuous_induced_rng.mpr
    show Continuous (fun A : G => star (A : Matrix (Fin 2) (Fin 2) ℂ))
    exact continuous_subtype_val.star

instance : IsTopologicalGroup G where

lemma mem_su_iff (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ↔ A * star A = 1 ∧ A.det = 1 := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]

lemma isClosed_su : IsClosed (Matrix.specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
  have : (Matrix.specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) =
      {A | A * star A = 1} ∩ {A | A.det = 1} := by
    ext A; simp [mem_su_iff]
  rw [this]
  exact (isClosed_eq (continuous_id.mul continuous_star) continuous_const).inter
    (isClosed_eq (continuous_id.matrix_det) continuous_const)

lemma isCompact_su : IsCompact (Matrix.specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
  let K : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
    Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => Metric.closedBall (0 : ℂ) 1))
  have hK : IsCompact K :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))
  refine hK.of_isClosed_subset isClosed_su ?_
  intro A hA i _ j _
  have hU : A ∈ Matrix.unitaryGroup (Fin 2) ℂ := (Matrix.mem_specialUnitaryGroup_iff.mp hA).1
  simpa using entry_norm_bound_of_unitary hU i j

instance : CompactSpace G := isCompact_iff_compactSpace.mp isCompact_su

/-! ### Connectedness: image of `S³` -/

/-- `φ(p) = [[a, −b̄], [b, ā]]` with `a = p₀ + i p₁`, `b = p₂ + i p₃`. -/
def phi (p : EuclideanSpace ℝ (Fin 4)) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(⟨p 0, p 1⟩ : ℂ), -(starRingEnd ℂ) ⟨p 2, p 3⟩; ⟨p 2, p 3⟩, (starRingEnd ℂ) ⟨p 0, p 1⟩]

lemma continuous_mkC {f g : EuclideanSpace ℝ (Fin 4) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun p => (⟨f p, g p⟩ : ℂ)) :=
  (Complex.equivRealProdCLM.symm.continuous).comp (hf.prodMk hg)

lemma continuous_phi : Continuous phi := by
  have hc : ∀ i : Fin 4, Continuous (fun p : EuclideanSpace ℝ (Fin 4) => p i) := fun i =>
    (EuclideanSpace.proj i).continuous
  have ha := continuous_mkC (hc 0) (hc 1)
  have hb := continuous_mkC (hc 2) (hc 3)
  refine continuous_pi (fun i => continuous_pi (fun j => ?_))
  fin_cases i <;> fin_cases j
  · exact ha
  · exact (Complex.continuous_conj.comp hb).neg
  · exact hb
  · exact Complex.continuous_conj.comp ha

lemma sum_sq_of_sphere {p : EuclideanSpace ℝ (Fin 4)}
    (hp : p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 = 1 := by
  have h : ‖p‖ = 1 := by simpa using hp
  have h2 : ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    simp [Fin.sum_univ_four, Real.norm_eq_abs, sq_abs]
  rw [h] at h2; linarith

lemma phi_mem {p : EuclideanSpace ℝ (Fin 4)}
    (hp : p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    phi p ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hs := sum_sq_of_sphere hp
  rw [mem_su_iff]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [phi, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff, Matrix.star_apply] <;>
      constructor <;> nlinarith [hs]
  · rw [Matrix.det_fin_two]
    simp [phi, Complex.ext_iff]
    constructor <;> nlinarith [hs]

lemma phi_surj {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, phi p = A := by
  rw [mem_su_iff] at hA
  obtain ⟨hU, hD⟩ := hA
  have hinv : A⁻¹ = star A := Matrix.inv_eq_right_inv hU
  have hadj : A⁻¹ = A.adjugate := by rw [Matrix.inv_def, hD]; simp
  have hstar : star A = A.adjugate := hinv.symm.trans hadj
  have e00 : (starRingEnd ℂ) (A 0 0) = A 1 1 := by
    have := congrFun (congrFun hstar 0) 0
    simpa [Matrix.star_apply, Matrix.adjugate_fin_two] using this
  have e10 : (starRingEnd ℂ) (A 0 1) = -A 1 0 := by
    have := congrFun (congrFun hstar 1) 0
    simpa [Matrix.star_apply, Matrix.adjugate_fin_two] using this
  have hU00 : A 0 0 * (starRingEnd ℂ) (A 0 0) + A 0 1 * (starRingEnd ℂ) (A 0 1) = 1 := by
    have := congrFun (congrFun hU 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] using this
  have h10 : A 1 0 = -(starRingEnd ℂ) (A 0 1) := by rw [e10, neg_neg]
  have h11 : A 1 1 = (starRingEnd ℂ) (A 0 0) := e00.symm
  have h01 : A 0 1 = -(starRingEnd ℂ) (A 1 0) := by rw [h10]; simp
  have hre := congrArg Complex.re hU00
  simp [Complex.mul_re] at hre
  have hr10 : (A 1 0).re = -(A 0 1).re := by rw [h10]; simp
  have hi10 : (A 1 0).im = (A 0 1).im := by rw [h10]; simp
  let p : EuclideanSpace ℝ (Fin 4) :=
    WithLp.toLp 2 ![(A 0 0).re, (A 0 0).im, (A 1 0).re, (A 1 0).im]
  refine ⟨p, ?_, ?_⟩
  · have hsum : ∑ i, ‖p i‖ ^ 2 = 1 := by
      simp [p, Fin.sum_univ_four, Real.norm_eq_abs, sq_abs, hr10, hi10]
      nlinarith [hre]
    have : ‖p‖ = 1 := by rw [EuclideanSpace.norm_eq, hsum, Real.sqrt_one]
    simpa using this
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [phi, p, h11, h01, Complex.ext_iff]

lemma isConnected_sphere3 : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
  apply isConnected_sphere _ 0 zero_le_one
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace, Fintype.card_fin]
  norm_num

instance : ConnectedSpace G := by
  rw [connectedSpace_iff_univ]
  have hS : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := isConnected_sphere3
  let ψ : EuclideanSpace ℝ (Fin 4) → Matrix (Fin 2) (Fin 2) ℂ := phi
  -- univ = image of the sphere under the corestriction of φ
  have himage : (Set.univ : Set G) =
      (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 => (⟨phi p.1, phi_mem p.2⟩ : G)) ''
        Set.univ := by
    ext A
    simp only [Set.mem_univ, Set.image_univ, Set.mem_range, true_iff]
    obtain ⟨p, hp, hpA⟩ := phi_surj A.2
    exact ⟨⟨p, hp⟩, Subtype.ext hpA⟩
  rw [himage]
  haveI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
    isConnected_iff_connectedSpace.mp hS
  apply isConnected_univ.image
  apply Continuous.continuousOn
  exact Continuous.subtype_mk (continuous_phi.comp continuous_subtype_val) _

/-! ### Inclusion into `U(2)` -/

/-- The inclusion `SU(2) → U(2)`. -/
def ρ : G →* Matrix.unitaryGroup (Fin 2) ℂ :=
  Submonoid.inclusion Matrix.specialUnitaryGroup_le_unitaryGroup

lemma ρ_coe (A : G) : ((ρ A : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = A := rfl

lemma ρ_continuous : Continuous ρ := by
  apply continuous_induced_rng.mpr
  exact continuous_subtype_val

lemma ρ_injective : Function.Injective ρ := by
  intro A B h
  apply Subtype.ext
  have := congrArg (fun U : Matrix.unitaryGroup (Fin 2) ℂ => (U : Matrix (Fin 2) (Fin 2) ℂ)) h
  simpa [ρ_coe] using this

end SU2

end ClayYM
