#!/usr/bin/env bash
# Build ClayYM from this directory and audit its axioms; then re-run the SymPy check of the fingerprint
# constants and compare its output with the committed reference (diff).
# Requirements: elan (https://github.com/leanprover/elan), git, network access for the first run;
# python3 with SymPy (which brings mpmath) for the constants check.
# v1.1: also checks the named hypothesis (OS reconstruction) of the conditional theorems, the literals of the
# q-form, and runs the mutation tests of scripts/mutants.py (every mutant must break the build).
# Set CLAYYM_SKIP_CACHE_GET=1 to skip `lake exe cache get` when Mathlib is already built locally.
# Exit code 0 only if every check passes.
set -u
cd "$(dirname "$0")/.." || exit 99
mkdir -p logs
fail=0
echo "Toolchain: $(cat lean-toolchain)"
if [ "${CLAYYM_SKIP_CACHE_GET:-0}" = "1" ]; then
  echo "lake exe cache get   SKIPPED (CLAYYM_SKIP_CACHE_GET=1: Mathlib already built locally)"
else
  lake exe cache get > logs/cache_get.log 2>&1;          rc=$?; echo "lake exe cache get   RC=$rc"; [ $rc -eq 0 ] || fail=1
fi
lake build ClayYM > logs/build_lib.log 2>&1;            rc=$?; echo "lake build ClayYM    RC=$rc"; [ $rc -eq 0 ] || fail=1
lake build ClayYM.Audit > logs/build_audit.log 2>&1;    rc=$?; echo "lake build Audit     RC=$rc"; [ $rc -eq 0 ] || fail=1
lake env lean scripts/AuditAll.lean > logs/audit_all.log 2>&1; rc=$?; echo "AuditAll.lean        RC=$rc"; [ $rc -eq 0 ] || fail=1
n_err=$(grep -c "error" logs/build_lib.log logs/build_audit.log logs/audit_all.log | awk -F: '{s+=$2} END {print s}')
n_sorry=$(grep -c "declaration uses .sorry.\|sorryAx" logs/build_lib.log logs/build_audit.log logs/audit_all.log | awk -F: '{s+=$2} END {print s}')
n_print=$(grep -c "depends on axioms" logs/build_audit.log)
n_nonstd_print=$(grep "depends on axioms" logs/build_audit.log | grep -v -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]")
echo "lines containing 'error'                 : $n_err"
echo "sorry occurrences                         : $n_sorry"
echo "#print axioms lines in ClayYM.Audit       : $n_print (non-standard: $n_nonstd_print)"
grep -E "AUDIT ClayYM|NON-STANDARD|AXIOM DECLARATION|STATEMENT" logs/audit_all.log | sed 's/^.*info: //'
[ "$n_err" -eq 0 ] || fail=1
[ "$n_sorry" -eq 0 ] || fail=1
[ "$n_nonstd_print" -eq 0 ] || fail=1
grep -q "0 axiom declarations, 0 constants with non-standard axioms" logs/audit_all.log || fail=1
[ "$(grep -c 'definition (Prop), OK' logs/audit_all.log)" -eq 3 ] || fail=1
# Fingerprint constants: the script prints to stdout only and never writes its reference file.
if python3 -c "import sympy, mpmath" > /dev/null 2>&1; then
  python3 constants/sympy_constantes.py > logs/constantes_obtenues.txt 2> logs/constantes_stderr.log; rc=$?
  echo "sympy_constantes.py  RC=$rc"; [ $rc -eq 0 ] || fail=1
  if diff -u constants/constantes_verifiees.txt logs/constantes_obtenues.txt > logs/constantes_diff.txt; then
    echo "constants: output identical to constants/constantes_verifiees.txt"
  else
    echo "constants: output DIFFERS from constants/constantes_verifiees.txt (see logs/constantes_diff.txt)"; fail=1
  fi
else
  echo "constants: python3 with sympy and mpmath not found, check not run"; fail=1
fi
# Tripwire: the Lean literals of the fingerprint must be exactly the values checked by the SymPy script above
# (otherwise only a human reading would link the two). This does NOT prove the physical values are right.
grep -qF 'def traceAnomalyCoeff (K : CompactSimpleGroup) : ℝ := 3 * K.dim / Real.pi ^ 4' ClayYM/Fingerprint.lean || { echo "literal kappa changed"; fail=1; }
grep -qF '(𝓝[≠] 0) (𝓝 (-(102 / 121)))' ClayYM/Fingerprint.lean || { echo "literal FP2 changed"; fail=1; }
grep -qF '(𝓝 ((K.dim : ℝ) * (4 / Real.pi ^ 4) * confI u μ ν ρ σ))' ClayYM/Fingerprint.lean || { echo "literal FP3 changed"; fail=1; }
grep -qF 'def b0 (CA : ℝ) : ℝ := 11 / 3 * CA' ClayYM/Group.lean || { echo "literal b0 changed"; fail=1; }
grep -qF 'def b1 (CA : ℝ) : ℝ := 34 / 3 * CA ^ 2' ClayYM/Group.lean || { echo "literal b1 changed"; fail=1; }
# v1.1 — named hypothesis. The OS reconstruction is a structure passed as an explicit argument (never an axiom):
# it must appear in the statements of the conditional theorems, and in none of the unconditional ones.
for n in ClayYM.QGap.hasMassGap ClayYM.QGap.hasMassGap_univ ClayYM.exists_hasMassGap_iff_exists_qGap \
         ClayYM.hasMassGap_iff_opNorm ClayYM.QGap.vacuum_unique ClayYM.hasMassGap_of_tendsto \
         ClayYM.vacuum_unique_of_tendsto ClayYM.Transfer.Recon.massGapOn_of_qGapOn ClayYM.Transfer.Recon.vacuum_unique; do
  sed 's/^.*info: //' logs/audit_all.log | grep -qx "NAMED HYPOTHESIS USED BY: $n" || { echo "named hypothesis missing in $n"; fail=1; }
done
for n in ClayYM.QGap.of_tendsto ClayYM.HasMassGap.qGap ClayYM.normalized_of_tendsto ClayYM.Transfer.QGapOn.of_tendsto \
         ClayYM.Transfer.MassGapOn.qGapOn ClayYM.Transfer.decay_of_qbound ClayYM.Ladder.truncation_inference_fails \
         ClayYM.Ladder.closure_needs_same_q ClayYM.trivS_conditional_chain; do
  sed 's/^.*info: //' logs/audit_all.log | grep -qx "NAMED HYPOTHESIS USED BY: $n" && { echo "unexpected named hypothesis in $n"; fail=1; }
done
echo "named hypothesis (OSReconstruction): $(sed 's/^.*info: //' logs/audit_all.log | grep -c '^NAMED HYPOTHESIS USED BY: ') theorem statements mention it"
# v1.1 — literals of the q-form and of the mass gap (the text quoted in STATEMENT.md, section 3.4).
grep -qF '  A ++ Family.smul (-(rpForm R S (vac ι) A 0)) (vac ι)' ClayYM/GapQ.lean || { echo "literal truncFam changed"; fail=1; }
grep -qF '  0 < ℓ ∧ 0 < q ∧ q < 1 ∧ ∀ A ∈ 𝒜₀,' ClayYM/GapQ.lean || { echo "literal QGap changed"; fail=1; }
grep -qF '    rpForm R S (truncFam R S A) (truncFam R S A) ℓ ≤' ClayYM/GapQ.lean || { echo "literal QGap inequality changed"; fail=1; }
grep -qF '      q * rpForm R S (truncFam R S A) (truncFam R S A) 0' ClayYM/GapQ.lean || { echo "literal QGap right-hand side changed"; fail=1; }
grep -qF '      Real.exp (-(Δ * t)) * Real.sqrt (rpForm R S F F 0) * Real.sqrt (rpForm R S G G 0)' ClayYM/Gap.lean || { echo "literal HasMassGap changed"; fail=1; }
# v1.1 — mutation tests: every mutant of scripts/mutants.py must break the build of its target declaration.
python3 scripts/mutants.py > logs/mutants.log 2>&1; rc=$?
echo "mutants.py           RC=$rc ; $(grep '^MUTANTS:' logs/mutants.log)"
[ $rc -eq 0 ] || fail=1
grep -q "^MUTATION TESTS: PASS" logs/mutants.log || fail=1
if [ $fail -eq 0 ]; then echo "VERIFY: PASS"; else echo "VERIFY: FAIL (see logs/)"; fi
exit $fail
