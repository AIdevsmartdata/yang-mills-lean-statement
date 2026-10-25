/-
ClayYM/GapQ.lean  (v1.1)
========================
The q-form of the mass gap for the Schwinger kernels of `ClayYM`, its equivalence with `HasMassGap`
(and with the operator form `‖e^{-tH}(1 − P_Ω)‖ ≤ e^{-Δt}`), the CLOSURE LEMMA, and the uniqueness
of the vacuum. Abstract proofs: `ClayYM/Transfer.lean`.

No axiom, no `sorry`. The Osterwalder–Schrader reconstruction is the NAMED HYPOTHESIS
`OSReconstruction R S` (= `Transfer.Recon (famOps ι d) (rpForm R S)`): an explicit argument of the
conditional theorems, never asserted. Its satisfiability is checked on the trivial theory
(`trivRecon`); for a genuine OS theory it is the content of the OS reconstruction theorem
(OS 1973/1975), which is NOT formalised.

* `QGap R S 𝒜₀ ℓ q` : `0 < ℓ`, `0 < q < 1` and `⟨v_A, e^{-ℓH} v_A⟩ ≤ q ‖v_A‖²` for every `A ∈ 𝒜₀`,
  with `v_A = A − ⟨Ω, A⟩ Ω` the family `truncFam R S A`; the gap statement is `∃ q, QGap R S 𝒜₀ ℓ q`.
* `HasMassGap.qGap`          : `HasMassGap R S Δ` ⟹ `QGap R S 𝒜₀ ℓ (e^{−Δℓ})`  (OS axioms only);
* `QGap.hasMassGap`          : `QGap R S 𝒜₀ ℓ q` + density ⟹ `HasMassGap R S (−log q / ℓ)`
                               (named hypothesis `OSReconstruction`);
* `exists_hasMassGap_iff_exists_qGap` : the equivalence, for every fixed `ℓ > 0`;
* `hasMassGap_iff_opNorm`    : `HasMassGap R S Δ` ⟺ `0 < Δ ∧ ∀ t ≥ 0, ‖e^{-tH}(1 − P_Ω)‖ ≤ e^{-Δt}`;
* `QGap.of_tendsto`          : CLOSURE LEMMA (no hypothesis beyond pointwise convergence on
                               `𝒜₀ ∪ {Ω}` and the SAME `q`);
* `hasMassGap_of_tendsto`, `vacuum_unique_of_tendsto` : gap and unique vacuum of the limit, under
                               the named hypothesis for the LIMIT theory only;
* `QGap.vacuum_unique`       : the uniqueness of the vacuum is a CONSEQUENCE of the q-form plus
                               density, not an extra hypothesis.
-/
import ClayYM.Transfer
import ClayYM.Fake.Trivial

open MeasureTheory Filter Topology
open scoped ContDiff RealInnerProductSpace

noncomputable section

namespace ClayYM

variable {ι : Type} {d : ℕ}

/-! ### Formal operations on families -/

/-- Scaling of a test function by `c`. -/
def PosTest.smul [NeZero d] {n : ℕ} (c : ℝ) (f : PosTest d n) : PosTest d n where
  toFun := fun x => c * f x
  smooth := contDiff_const.mul f.smooth
  compact := HasCompactSupport.mul_left (f := fun _ => c) f.compact
  supp := tsupport_mul_subset_right.trans f.supp

/-- Scaling of a term (same number of points, same labels). -/
def Term.smul [NeZero d] (c : ℝ) (a : Term ι d) : Term ι d := ⟨a.n, a.labels, a.f.smul c⟩

/-- Scaling of a family (every term is scaled). -/
def Family.smul [NeZero d] (c : ℝ) (F : Family ι d) : Family ι d := F.map (Term.smul c)

/-- Formal operations on families: concatenation (formal sum), scaling, vacuum `vac`. -/
def famOps (ι : Type) (d : ℕ) [NeZero d] : Transfer.VecOps (Family ι d) where
  add := fun F G => F ++ G
  smul := Family.smul
  Ω := vac ι

variable [Fintype ι] [NeZero d]

lemma rpForm_append_left (R : CompRep ι d) (S : Schwinger ι d) (F F' G : Family ι d) (t : ℝ) :
    rpForm R S (F ++ F') G t = rpForm R S F G t + rpForm R S F' G t := by
  unfold rpForm
  rw [List.map_append, List.sum_append]

lemma rpForm_append_right (R : CompRep ι d) (S : Schwinger ι d) (F G G' : Family ι d) (t : ℝ) :
    rpForm R S F (G ++ G') t = rpForm R S F G t + rpForm R S F G' t := by
  unfold rpForm
  simp only [List.map_append, List.sum_append]
  exact List.sum_map_add

lemma term_integral_smul_left (R : CompRep ι d) (S : Schwinger ι d) (c : ℝ) (a b : Term ι d)
    (t : ℝ) :
    (∫ x, ∫ y, (Term.smul c a).f x * b.f y * rpKernel R S (Term.smul c a) b t x y) =
      c * ∫ x, ∫ y, a.f x * b.f y * rpKernel R S a b t x y := by
  rw [← integral_const_mul]
  congr 1
  ext x
  rw [← integral_const_mul]
  congr 1
  ext y
  show c * a.f x * b.f y * rpKernel R S a b t x y = c * (a.f x * b.f y * rpKernel R S a b t x y)
  ring

lemma term_integral_smul_right (R : CompRep ι d) (S : Schwinger ι d) (c : ℝ) (a b : Term ι d)
    (t : ℝ) :
    (∫ x, ∫ y, a.f x * (Term.smul c b).f y * rpKernel R S a (Term.smul c b) t x y) =
      c * ∫ x, ∫ y, a.f x * b.f y * rpKernel R S a b t x y := by
  rw [← integral_const_mul]
  congr 1
  ext x
  rw [← integral_const_mul]
  congr 1
  ext y
  show a.f x * (c * b.f y) * rpKernel R S a b t x y = c * (a.f x * b.f y * rpKernel R S a b t x y)
  ring

lemma rpForm_smul_left (R : CompRep ι d) (S : Schwinger ι d) (c : ℝ) (F G : Family ι d) (t : ℝ) :
    rpForm R S (Family.smul c F) G t = c * rpForm R S F G t := by
  unfold rpForm Family.smul
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun a _ => ?_
  simp only [Function.comp_apply]
  rw [← List.sum_map_mul_left]
  congr 1
  exact List.map_congr_left fun b _ => term_integral_smul_left R S c a b t

lemma rpForm_smul_right (R : CompRep ι d) (S : Schwinger ι d) (c : ℝ) (F G : Family ι d) (t : ℝ) :
    rpForm R S F (Family.smul c G) t = c * rpForm R S F G t := by
  unfold rpForm Family.smul
  rw [← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun a _ => ?_
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  exact List.map_congr_left fun b _ => term_integral_smul_right R S c a b t

/-- The OS form is bilinear for concatenation and scaling (no hypothesis on `S`). -/
theorem rpForm_isBilin (R : CompRep ι d) (S : Schwinger ι d) :
    Transfer.IsBilin (famOps ι d) (rpForm R S) where
  add_left := rpForm_append_left R S
  add_right := rpForm_append_right R S
  smul_left := rpForm_smul_left R S
  smul_right := rpForm_smul_right R S

/-- `⟨Ω, e^{-tH} Ω⟩ = S(∅)` for every `t`. -/
lemma rpForm_vac_vac (R : CompRep ι d) (S : Schwinger ι d) (t : ℝ) :
    rpForm R S (vac ι) (vac ι) t = S [] := by
  simp [rpForm, vac, vacTerm, vacTest, rpKernel, mkList, integral_const,
    volume_real_config_zero_univ]

lemma famOps_vac_vac (R : CompRep ι d) (S : Schwinger ι d) (hnorm : S [] = 1) :
    rpForm R S (famOps ι d).Ω (famOps ι d).Ω 0 = 1 := by
  show rpForm R S (vac ι) (vac ι) 0 = 1
  rw [rpForm_vac_vac, hnorm]

/-- `HasMassGap` is the abstract mass gap of the OS form. -/
theorem hasMassGap_iff_massGapOn (R : CompRep ι d) (S : Schwinger ι d) (Δ : ℝ) :
    HasMassGap R S Δ ↔ Transfer.MassGapOn (famOps ι d) (rpForm R S) Set.univ Δ :=
  ⟨fun h => ⟨h.1, fun F _ G _ t ht => h.2 F G t ht⟩,
   fun h => ⟨h.1, fun F G t ht => h.2 F (Set.mem_univ _) G (Set.mem_univ _) t ht⟩⟩

/-! ### The q-form of the gap -/

/-- Truncated family `v_A = A − ⟨Ω, A⟩ Ω`: the family `A` followed by the vacuum term scaled by
`−⟨Ω, A⟩ = −rpForm R S (vac ι) A 0`. -/
def truncFam (R : CompRep ι d) (S : Schwinger ι d) (A : Family ι d) : Family ι d :=
  A ++ Family.smul (-(rpForm R S (vac ι) A 0)) (vac ι)

/-- **Mass gap, q-form.** At the physical time `ℓ > 0`, with `0 < q < 1`:
`⟨v_A, e^{-ℓH} v_A⟩ ≤ q ‖v_A‖²` for every `A ∈ 𝒜₀`, i.e.
`rpForm R S (truncFam R S A) (truncFam R S A) ℓ ≤ q * rpForm R S (truncFam R S A) (truncFam R S A) 0`.
The gap statement is `∃ q, QGap R S 𝒜₀ ℓ q` (one `q` for all `A`). -/
def QGap (R : CompRep ι d) (S : Schwinger ι d) (𝒜₀ : Set (Family ι d)) (ℓ q : ℝ) : Prop :=
  0 < ℓ ∧ 0 < q ∧ q < 1 ∧ ∀ A ∈ 𝒜₀,
    rpForm R S (truncFam R S A) (truncFam R S A) ℓ ≤
      q * rpForm R S (truncFam R S A) (truncFam R S A) 0

/-- `QGap` is the abstract q-form of the OS form (definitional bridge; tripwire for mutations). -/
theorem qGap_iff_qGapOn (R : CompRep ι d) (S : Schwinger ι d) (𝒜₀ : Set (Family ι d)) (ℓ q : ℝ) :
    QGap R S 𝒜₀ ℓ q ↔ Transfer.QGapOn (famOps ι d) (rpForm R S) 𝒜₀ ℓ q :=
  Iff.rfl

/-- **Gap ⟹ q-form** (OS axioms only: normalisation and reflection positivity). -/
theorem HasMassGap.qGap {R : CompRep ι d} {S : Schwinger ι d} {Δ ℓ : ℝ} (hOS : OSAxioms R S)
    (h : HasMassGap R S Δ) (hℓ : 0 < ℓ) (𝒜₀ : Set (Family ι d)) :
    QGap R S 𝒜₀ ℓ (Real.exp (-(Δ * ℓ))) :=
  Transfer.MassGapOn.qGapOn (rpForm_isBilin R S) (famOps_vac_vac R S hOS.normalized)
    hOS.reflection_positive ((hasMassGap_iff_massGapOn R S Δ).1 h) hℓ 𝒜₀

/-! ### The named hypothesis -/

/-- **NAMED HYPOTHESIS: Osterwalder–Schrader reconstruction of the theory `(R, S)`** (Hilbert space
and transfer semigroup). NOT proved; used only as an explicit argument. -/
abbrev OSReconstruction (R : CompRep ι d) (S : Schwinger ι d) : Type 1 :=
  Transfer.Recon (famOps ι d) (rpForm R S)

/-- Density of the truncated classes of `𝒜₀` in `Ω^⊥` (cyclicity of the vacuum for `𝒜₀`). -/
def TruncDense {R : CompRep ι d} {S : Schwinger ι d} (rec : OSReconstruction R S)
    (𝒜₀ : Set (Family ι d)) : Prop :=
  ∀ w : rec.H, ⟪rec.ω, w⟫ = 0 → w ∈ closure (rec.cls '' (truncFam R S '' 𝒜₀))

/-- For `𝒜₀ = univ` (all families) the density is automatic. -/
theorem truncDense_univ {R : CompRep ι d} {S : Schwinger ι d} (rec : OSReconstruction R S) :
    TruncDense rec Set.univ :=
  rec.truncDense_univ (rpForm_isBilin R S)

/-- **q-form ⟹ gap** `Δ = −log q / ℓ` (named hypothesis `OSReconstruction`, plus density). -/
theorem QGap.hasMassGap {R : CompRep ι d} {S : Schwinger ι d} {𝒜₀ : Set (Family ι d)} {ℓ q : ℝ}
    (rec : OSReconstruction R S) (hnorm : S [] = 1) (h : QGap R S 𝒜₀ ℓ q)
    (hd : TruncDense rec 𝒜₀) : HasMassGap R S (-Real.log q / ℓ) :=
  (hasMassGap_iff_massGapOn R S _).2 (rec.massGapOn_of_qGapOn (famOps_vac_vac R S hnorm) h hd)

theorem QGap.hasMassGap_univ {R : CompRep ι d} {S : Schwinger ι d} {ℓ q : ℝ}
    (rec : OSReconstruction R S) (hnorm : S [] = 1) (h : QGap R S Set.univ ℓ q) :
    HasMassGap R S (-Real.log q / ℓ) :=
  h.hasMassGap rec hnorm (truncDense_univ rec)

/-- **Equivalence** of the two forms of the gap, for every fixed `ℓ > 0`. -/
theorem exists_hasMassGap_iff_exists_qGap {R : CompRep ι d} {S : Schwinger ι d}
    (hOS : OSAxioms R S) (rec : OSReconstruction R S) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∃ Δ, HasMassGap R S Δ) ↔ ∃ q, QGap R S Set.univ ℓ q :=
  ⟨fun ⟨_, h⟩ => ⟨_, h.qGap hOS hℓ Set.univ⟩,
   fun ⟨_, h⟩ => ⟨_, h.hasMassGap_univ rec hOS.normalized⟩⟩

/-- The two constructions are inverse to each other: `Δ ↦ q = e^{−Δℓ} ↦ −log q / ℓ = Δ`. -/
lemma neg_log_exp_div {Δ ℓ : ℝ} (hℓ : 0 < ℓ) : -Real.log (Real.exp (-(Δ * ℓ))) / ℓ = Δ := by
  rw [Real.log_exp, neg_neg, mul_div_assoc, div_self hℓ.ne', mul_one]

/-- **Operator form** (named hypothesis): `HasMassGap R S Δ` ⟺
`0 < Δ ∧ ∀ t ≥ 0, ‖e^{-tH}(1 − P_Ω)‖ ≤ e^{-Δt}`. -/
theorem hasMassGap_iff_opNorm {R : CompRep ι d} {S : Schwinger ι d} (rec : OSReconstruction R S)
    (hnorm : S [] = 1) (Δ : ℝ) :
    HasMassGap R S Δ ↔ 0 < Δ ∧ ∀ t, 0 ≤ t → ‖(rec.T t).comp rec.perp‖ ≤ Real.exp (-(Δ * t)) :=
  (hasMassGap_iff_massGapOn R S Δ).trans (rec.massGapOn_univ_iff_opNorm (famOps_vac_vac R S hnorm) Δ)

/-- **Uniqueness of the vacuum** follows from the q-form and density (no extra hypothesis):
every vector fixed by `e^{-ℓH}` is a multiple of `Ω`. -/
theorem QGap.vacuum_unique {R : CompRep ι d} {S : Schwinger ι d} {𝒜₀ : Set (Family ι d)}
    {ℓ q : ℝ} (rec : OSReconstruction R S) (hnorm : S [] = 1) (h : QGap R S 𝒜₀ ℓ q)
    (hd : TruncDense rec 𝒜₀) (w : rec.H) (hw : rec.T ℓ w = w) : w = ⟪rec.ω, w⟫ • rec.ω :=
  rec.vacuum_unique (famOps_vac_vac R S hnorm) h hd w hw

/-! ### Closure lemma -/

/-- Pointwise ("simple") convergence of the Schwinger functions on `𝒜₀`: convergence of the
smeared values `⟪F, τ_t G⟫ = rpForm R (Sk k) F G t` for `F, G ∈ 𝒜₀ ∪ {Ω}` and `t ∈ {0, ℓ}`. -/
def SchwingerConvergesOn {α : Type*} (L : Filter α) (R : CompRep ι d) (Sk : α → Schwinger ι d)
    (S : Schwinger ι d) (𝒜₀ : Set (Family ι d)) (ℓ : ℝ) : Prop :=
  ∀ F ∈ insert (vac ι) 𝒜₀, ∀ G ∈ insert (vac ι) 𝒜₀, ∀ t ∈ ({0, ℓ} : Set ℝ),
    Tendsto (fun k => rpForm R (Sk k) F G t) L (𝓝 (rpForm R S F G t))

/-- **CLOSURE LEMMA.** If Schwinger functions converge pointwise on `𝒜₀` and (eventually) satisfy
the truncated inequality with the SAME `q`, their limit satisfies it. Any filter: sequences,
subsequences, nets. No OS axiom and no reconstruction is used. -/
theorem QGap.of_tendsto {α : Type*} {L : Filter α} [L.NeBot] {R : CompRep ι d}
    {Sk : α → Schwinger ι d} {S : Schwinger ι d} {𝒜₀ : Set (Family ι d)} {ℓ q : ℝ}
    (hconv : SchwingerConvergesOn L R Sk S 𝒜₀ ℓ) (h : ∀ᶠ k in L, QGap R (Sk k) 𝒜₀ ℓ q) :
    QGap R S 𝒜₀ ℓ q :=
  Transfer.QGapOn.of_tendsto (fun k => rpForm_isBilin R (Sk k)) (rpForm_isBilin R S) hconv h

/-- The normalisation `S(∅) = 1` passes to the limit. -/
theorem normalized_of_tendsto {α : Type*} {L : Filter α} [L.NeBot] {R : CompRep ι d}
    {Sk : α → Schwinger ι d} {S : Schwinger ι d} {𝒜₀ : Set (Family ι d)} {ℓ : ℝ}
    (hconv : SchwingerConvergesOn L R Sk S 𝒜₀ ℓ) (hn : ∀ᶠ k in L, Sk k [] = 1) : S [] = 1 := by
  have h := hconv (vac ι) (Set.mem_insert _ _) (vac ι) (Set.mem_insert _ _) 0 (by simp)
  simp only [rpForm_vac_vac] at h
  exact tendsto_nhds_unique h (tendsto_const_nhds.congr' (hn.mono fun k hk => hk.symm))

/-- **Closure + gap.** Approximants with the SAME `q`, converging pointwise on `𝒜₀`: the limit has
the mass gap `−log q / ℓ`, under the named hypothesis for the LIMIT theory and the density of the
truncated classes of `𝒜₀` (automatic for `𝒜₀ = univ`). -/
theorem hasMassGap_of_tendsto {α : Type*} {L : Filter α} [L.NeBot] {R : CompRep ι d}
    {Sk : α → Schwinger ι d} {S : Schwinger ι d} {𝒜₀ : Set (Family ι d)} {ℓ q : ℝ}
    (hconv : SchwingerConvergesOn L R Sk S 𝒜₀ ℓ) (hq : ∀ᶠ k in L, QGap R (Sk k) 𝒜₀ ℓ q)
    (hn : ∀ᶠ k in L, Sk k [] = 1) (rec : OSReconstruction R S) (hd : TruncDense rec 𝒜₀) :
    HasMassGap R S (-Real.log q / ℓ) :=
  (QGap.of_tendsto hconv hq).hasMassGap rec (normalized_of_tendsto hconv hn) hd

/-- **Closure + unique vacuum.** Same hypotheses: every vector of the limit theory fixed by
`e^{-ℓH}` is a multiple of `Ω`. No uniqueness of the vacuum is assumed. -/
theorem vacuum_unique_of_tendsto {α : Type*} {L : Filter α} [L.NeBot] {R : CompRep ι d}
    {Sk : α → Schwinger ι d} {S : Schwinger ι d} {𝒜₀ : Set (Family ι d)} {ℓ q : ℝ}
    (hconv : SchwingerConvergesOn L R Sk S 𝒜₀ ℓ) (hq : ∀ᶠ k in L, QGap R (Sk k) 𝒜₀ ℓ q)
    (hn : ∀ᶠ k in L, Sk k [] = 1) (rec : OSReconstruction R S) (hd : TruncDense rec 𝒜₀)
    (w : rec.H) (hw : rec.T ℓ w = w) : w = ⟪rec.ω, w⟫ • rec.ω :=
  (QGap.of_tendsto hconv hq).vacuum_unique rec (normalized_of_tendsto hconv hn) hd w hw

/-! ### Non-vacuity of the named hypothesis (trivial theory) -/

/-- The trivial theory has an OS reconstruction (`H = ℝ`, `e^{-tH} = 1`): the named hypothesis is
satisfiable (all its fields, completeness and strong continuity included). -/
def trivRecon (R : CompRep ι d) : OSReconstruction R (trivS ι d) where
  H := ℝ
  cls := trivAmp
  T := fun _ => ContinuousLinearMap.id ℝ ℝ
  inner_cls := by
    intro F G
    rw [rpForm_trivS]
    simp [mul_comm]
  inner_T := by
    intro F G t _
    rw [rpForm_trivS]
    simp [mul_comm]
  T_add := by
    intro s t _ _
    exact (ContinuousLinearMap.id_comp _).symm
  T_symm := by
    intro t _ x y
    simp
  T_contr := by
    intro t _
    exact ContinuousLinearMap.norm_id_le
  T_vac := by
    intro t _
    simp
  T_cont := by
    intro x
    exact tendsto_const_nhds
  dense := by
    apply Function.Surjective.denseRange
    intro r
    refine ⟨Family.smul r (vac ι), ?_⟩
    simp [trivAmp, Family.smul, vac, vacTerm, Term.smul, PosTest.smul, vacTest, integral_const,
      volume_real_config_zero_univ]

/-- The trivial theory satisfies the q-form for every `q ∈ (0,1)` (its truncated vectors vanish). -/
theorem trivS_qGap (R : CompRep ι d) {ℓ q : ℝ} (hℓ : 0 < ℓ) (hq : 0 < q) (hq1 : q < 1) :
    QGap R (trivS ι d) Set.univ ℓ q := by
  refine ⟨hℓ, hq, hq1, fun A _ => ?_⟩
  show rpForm R (trivS ι d) ((famOps ι d).trunc _ A) ((famOps ι d).trunc _ A) ℓ ≤
    q * rpForm R (trivS ι d) ((famOps ι d).trunc _ A) ((famOps ι d).trunc _ A) 0
  rw [(rpForm_isBilin R _).trunc_trunc, (rpForm_isBilin R _).trunc_trunc]
  simp only [Transfer.truncCorr, famOps, rpForm_trivS, trivAmp_vac]
  ring_nf
  exact le_refl _

/-- Sanity check of the whole conditional chain on the trivial theory: every hypothesis of
`QGap.hasMassGap_univ` is satisfiable simultaneously, and its conclusion agrees with
`trivS_hasMassGap`. -/
theorem trivS_conditional_chain (R : CompRep ι d) {ℓ q : ℝ} (hℓ : 0 < ℓ) (hq : 0 < q)
    (hq1 : q < 1) : HasMassGap R (trivS ι d) (-Real.log q / ℓ) :=
  (trivS_qGap R hℓ hq hq1).hasMassGap_univ (trivRecon R) (trivS_OSAxioms R).normalized

end ClayYM
