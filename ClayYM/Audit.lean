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
-- The open statements are definitions of type `Prop` (no `theorem … := sorry`)
#check (ClayYM.ClayYM_A : Prop)
#check (ClayYM.ClayYM_B : Prop)
#check (ClayYM.ClayYM_AB : Prop)
