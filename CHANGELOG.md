# Changelog

## v1.1.0 (2026-10-25)
Archived on Zenodo: doi:10.5281/zenodo.23650415.

### Added
- `QGap`: the mass gap in the form `∃ q < 1, ∀ A ∈ 𝒜₀, ⟨v_A, e^{−ℓH} v_A⟩ ≤ q‖v_A‖²`, and its equivalence with `HasMassGap`
  in both directions. `HasMassGap.qGap` uses only the OS axioms; `QGap.hasMassGap` uses the named hypothesis
  `OSReconstruction` (real Hilbert space, C₀ semigroup of self-adjoint contractions, dense classes) and density.
  `OSReconstruction` is never an axiom; it appears in the statements of the conditional theorems only.
- `hasMassGap_iff_opNorm`: equivalence with the operator form `‖e^{−tH}(1 − P_Ω)‖ ≤ e^{−Δt}`.
- `QGap.of_tendsto`: closure lemma. Pointwise limits (along any non-trivial filter) of Schwinger functions that satisfy the
  q-form with the same q satisfy it. It uses neither the OS axioms nor reconstruction.
- Uniqueness of the vacuum as a consequence of the q-form. Compiled countermodels show that density is necessary
  (`HiddenVacuum.density_needed`) and that a unique vacuum does not replace it (`HiddenSlowMode.density_needed_unique_vacuum`);
  these countermodels are abstract (ℝ³), not Schwinger kernels.
- Quantifier guard `SpectralLadder` (H e_n = e_n/n): each truncation has a gap but the limit does not
  (`truncation_inference_fails`); the closure requires the same q (`closure_needs_same_q`).
- STATEMENT.md §6.10, residual gaps: θ = π (topological phase, variant B only); B₆, C₆ and E₆ have the same dimension 78
  (dual Coxeter numbers 11, 7 and 12) and are not distinguished by variant B alone (variant AB separates them); the OPE is not formalised.
- Verification: `scripts/AuditAll.lean` (axioms of every declaration and the named-hypothesis audit), `scripts/mutants.py`
  (32 mutants, each must fail inside a designated declaration), optional flag `CLAYYM_SKIP_CACHE_GET=1` in `scripts/verify.sh`.

### Corrected (errata to the v1.0.0 text)
- The GKKS anomaly argument (Gaiotto–Kapustin–Komargodski–Seiberg, JHEP 05 (2017) 091) was stated for all gauge groups.
  It applies to SU(N) (STATEMENT.md §3.5).
- v1.0.0 attributed to `HasMassGap` the rejection of a pure CP-breaking phase at θ = π. `HasMassGap` rejects a degenerate
  vacuum; a pure CP-breaking state is only in tension with the full O(4) covariance of `OSAxioms`, which is an argument,
  not a theorem (STATEMENT.md §4).

### Unchanged
- The definitions of the three statements (A, B, AB) and of `HasMassGap`, and the 44 guards of v1.0.0.
- This is not a proof and not progress on the problem: v1.1.0 gives no mechanism for the uniformity of q.

## v1.0.0 (2026-10-25)
- Initial release: candidate statements A, B and AB, guard theorems against fake models, axiom audit, SymPy check of the
  fingerprint constants. Archived on Zenodo: doi:10.5281/zenodo.23644080.
