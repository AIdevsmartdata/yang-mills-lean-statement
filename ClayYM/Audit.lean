/-
ClayYM/Audit.lean — `#print axioms` of every guard and every control theorem.
Expected: only `propext`, `Classical.choice`, `Quot.sound` (never `sorryAx`,
never `Lean.ofReduceBool`). The open statements are `def … : Prop` (checked by `#check`).
-/
import ClayYM

-- Fake model: trivial theory (OS framework, any dimension)
#print axioms ClayYM.trivS_OSAxioms
#print axioms ClayYM.trivS_hasMassGap
#print axioms ClayYM.trivS_not_finiteMass
#print axioms ClayYM.trivS_not_clayMassGap
-- Fake model: trivial theory against variants A and B
#print axioms ClayYM.trivS_TensorSymmetric
#print axioms ClayYM.trivS_Conserved
#print axioms ClayYM.trivS_WardEnergy
#print axioms ClayYM.trivS_not_UVTrace
#print axioms ClayYM.trivS_not_YMFingerprint
#print axioms ClayYM.trivS_not_ComponentsNontrivial
#print axioms ClayYM.trivS_not_B
#print axioms ClayYM.trivial_wilson_limit
-- Fake model: free gluons (mutation test of FP1)
#print axioms ClayYM.exactConformal_not_UVTrace
#print axioms ClayYM.exactConformal_UVStress
#print axioms ClayYM.freeGluons_mutation
#print axioms ClayYM.freeGluons_not_fingerprint_with
-- Fake model: free scalar field (Wick polynomials)
#print axioms ClayYM.wick_not_UVTrace
#print axioms ClayYM.gffKernel_lower
#print axioms ClayYM.gffKernel_upper
#print axioms ClayYM.gff_wick_not_UVTrace
-- Fake model: abelian group U(1)
#print axioms ClayYM.not_simple_dim_one
#print axioms ClayYM.CompactSimpleGroup.two_le_N
-- Fake model: 2D Yang–Mills (trivial local sector)
#print axioms ClayYM.ym2d_local_sector_not_finiteMass
#print axioms ClayYM.ym2d_local_sector_OS
-- Non-vacuity of the quantifier over groups: SU(2) inhabits the class
#print axioms ClayYM.compactSimpleGroup_nonempty
#print axioms ClayYM.SU2.dim_eq_three
#print axioms ClayYM.SU2.lieAlgebra_eq
#print axioms ClayYM.SU2.isSimpleLieAlg_su2
-- Decoupled sectors (adversarial review): additivity, and checks of `Decomposable`
#print axioms ClayYM.conn2_indepSum
#print axioms ClayYM.indepSum_trivS_left
#print axioms ClayYM.not_hasConnected_trivS
#print axioms ClayYM.CompactSimpleGroup.dim_pos
#print axioms ClayYM.traceAnomalyCoeff_pos
#print axioms ClayYM.traceAnomalyCoeff_add
#print axioms ClayYM.UVTrace_indepSum
#print axioms ClayYM.UVStress_indepSum
#print axioms ClayYM.uvFingerprint_indepSum
#print axioms ClayYM.indepSum_not_YMFingerprint
-- Checks
#print axioms ClayYM.HasMassGap.mono
#print axioms ClayYM.b1_div_b0_sq
#print axioms ClayYM.θc_eq
#print axioms ClayYM.confI_traceless
#print axioms ClayYM.ClayYM_AB.toA
#print axioms ClayYM.ClayYM_AB.toB
-- v1.1 — q-form of the gap, closure lemma, uniqueness of the vacuum (abstract layer)
#print axioms ClayYM.Transfer.IsBilin.trunc_trunc
#print axioms ClayYM.Transfer.QGapOn.of_tendsto
#print axioms ClayYM.Transfer.MassGapOn.qGapOn
#print axioms ClayYM.Transfer.decay_of_qbound
#print axioms ClayYM.Transfer.Recon.qbound
#print axioms ClayYM.Transfer.Recon.massGapOn_of_qGapOn
#print axioms ClayYM.Transfer.Recon.vacuum_unique
#print axioms ClayYM.Transfer.Recon.truncDense_univ
#print axioms ClayYM.Transfer.Recon.massGapOn_univ_iff_opNorm
-- v1.1 — the same results for the Schwinger kernels of ClayYM (named hypothesis: OSReconstruction)
#print axioms ClayYM.rpForm_isBilin
#print axioms ClayYM.rpForm_vac_vac
#print axioms ClayYM.hasMassGap_iff_massGapOn
#print axioms ClayYM.qGap_iff_qGapOn
#print axioms ClayYM.HasMassGap.qGap
#print axioms ClayYM.truncDense_univ
#print axioms ClayYM.QGap.hasMassGap
#print axioms ClayYM.QGap.hasMassGap_univ
#print axioms ClayYM.exists_hasMassGap_iff_exists_qGap
#print axioms ClayYM.neg_log_exp_div
#print axioms ClayYM.hasMassGap_iff_opNorm
#print axioms ClayYM.QGap.vacuum_unique
#print axioms ClayYM.QGap.of_tendsto
#print axioms ClayYM.normalized_of_tendsto
#print axioms ClayYM.hasMassGap_of_tendsto
#print axioms ClayYM.vacuum_unique_of_tendsto
#print axioms ClayYM.trivRecon
#print axioms ClayYM.trivS_qGap
#print axioms ClayYM.trivS_conditional_chain
-- v1.1 — guard (b): spectral ladder H e_n = e_n / n (every truncation gapped, not uniformly)
#print axioms ClayYM.Ladder.isBilin
#print axioms ClayYM.Ladder.trunc_qGap
#print axioms ClayYM.Ladder.not_qGap
#print axioms ClayYM.Ladder.truncation_inference_fails
#print axioms ClayYM.Ladder.trunc_massGap
#print axioms ClayYM.Ladder.not_massGap
#print axioms ClayYM.Ladder.approx_qGap
#print axioms ClayYM.Ladder.approx_converges
#print axioms ClayYM.Ladder.closure_needs_same_q
-- v1.1 — guard: hidden vacuum (non-cyclic algebra): density cannot be dropped
#print axioms ClayYM.HiddenVacuum.recon
#print axioms ClayYM.HiddenVacuum.isBilin
#print axioms ClayYM.HiddenVacuum.qGap
#print axioms ClayYM.HiddenVacuum.not_massGap
#print axioms ClayYM.HiddenVacuum.second_vacuum
#print axioms ClayYM.HiddenVacuum.density_needed
#print axioms ClayYM.HiddenVacuum.uniqueness_needs_density
-- The open statements are definitions of type `Prop` (no `theorem … := sorry`)
#check (ClayYM.ClayYM_A : Prop)
#check (ClayYM.ClayYM_B : Prop)
#check (ClayYM.ClayYM_AB : Prop)
