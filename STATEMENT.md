# ClayYM: a candidate Lean statement of the Clay problem "Yang–Mills existence and mass gap", with its fake models

Version of 2026-10-25. Lean 4 v4.34.0 + Mathlib v4.34.0 (rev `5ed2965256430c3649e86755f9576b54eca72435`); see `README.md`, "How to verify".

**Status.** This document describes a *candidate* formal statement and its compiled guards. It is not a proof and not progress on the problem. It has not been reviewed by an independent human expert. The Lean code and this text were written by AI agents (Claude, Anthropic) under the direction of the author; see `README.md`, "AI use". "We" below refers to this work.

## 0. Summary

1. The public Lean statements of the problem are not valid targets, and none of them comes with compiled guards.
   - The lean-dojo sketch is satisfied by a toy model: **we compiled one**, and its `ClayYangMills` is a theorem of Lean (§1.1; the witness is not included in this repository).
   - The copy used by math-challenge.org is **contradictory** (vacuum axiom). Its "prize" target is equivalent to "no compact simple gauge group exists", which is **proved and compiled** against their exact definitions (§1.2; the witness is public in issue #2 of that repository). Mathematically this is a false proposition (SU(2) satisfies the class; that instance is not built in Lean).
   - formal-conjectures (Google DeepMind) has no Yang–Mills file (checked on 2026-10-24). The only serious statement found, formalpedia, describes itself as "proxy, needs review".
2. This repository gives three statements, all of them `def … : Prop` (no `theorem … := sorry`):
   - `ClayYM_A`, the **Wilson lattice limit**: "this is Yang–Mills for G" is constructed;
   - `ClayYM_B`, the **axiomatic** variant: OS axioms, mass gap, 21 non-zero components, UV fingerprint of asymptotic freedom (coefficient κ = 3 dim G/π⁴ imposed) and indecomposability;
   - `ClayYM_AB`, the conjunction of the two, the **recommended reference statement** (§3.6).
3. The framework is Euclidean: Schwinger kernels off the diagonals, Osterwalder–Schrader axioms with the 1975 linear growth condition. The gap is written in Euclidean form; through OS reconstruction it is equivalent to `spec H ⊂ {0} ∪ [Δ,∞)` with a unique vacuum. The clause `m < ∞` comes from Jaffe–Witten.
4. Proved guards (`ClayYM/Audit.lean`): 44 theorems, depending only on `propext`, `Classical.choice`, `Quot.sound`, with 0 `sorry`. They were **re-checked by a second, independent kernel, nanoda** (51 133 declarations without error, negative witness rejected), and the rebuild from a clean copy of the sources is green. Fake models rejected:
   - the trivial theory;
   - the local sector of YM₂;
   - every Wick polynomial (without derivatives) of the massive free scalar field, for every mass m;
   - free gluons (and every conformal theory);
   - U(1);
   - every decoupled sum of two non-trivial OS theories, in particular the products `YM_{G₁} ⊗ YM_{G₂}` (clause `indecomposable`).
   Four mutation tests prove that clauses are **necessary**: `FiniteMass`, `ComponentsNontrivial`, FP1 in the presence of FP3, and `indecomposable` in the presence of FP1–FP3 (the UV fingerprint is additive: `uvFingerprint_indepSum`). Positive control: the class of groups is **inhabited by SU(2)** (with `dim = 3`), so the "∀ G" statements are not vacuously true.
5. **Main limitation of variant B.** The adversarial review showed that the first version of B (free FP1 coefficient K, no indecomposability) **reduced to SU(2)**: `YM_SU(2)` coupled to 12(dim G − 3) decoupled massive free scalars, or `YM_SU(2)^⊗q` with dim G = 3q, passed every clause. Two fixes were made: κ = 3 dim G/π⁴ is imposed, and the clause `indecomposable` is added.
   - After the fix, B still identifies G only up to `dim G` among SIMPLE groups: it lets through YM for another simple group of the same dimension (for example Spin(7) versus Sp(6)). Indeed b₀ and b₁ appear only through the universal ratio `b₁/b₀² = 102/121`, proved independent of G.
   - Three other limitations remain: B omits the C-odd sectors, leaves a loophole at θ = π (TQFT phase), and indecomposability is one more requirement to prove.
   - Hence the recommendation to take **AB as the reference statement**.
6. **Main limitation of variant A.** Its fidelity rests on the universality of lattice limits, which is a physical belief and not a theorem. The relevance of each clause rests on OS reconstruction, which is not formalised.

## 1. Existing formal statements and why they fail

### 1.1 lean-dojo/LeanMillenniumPrizeProblems (Apache-2.0)

Read at commit `603053dc` (2026-09-10): files `Problems/YangMills/{Quantum,Millennium}.lean` and `README.md`.

**What the repository says.** The README classifies Yang–Mills as "Statement incomplete, not a valid target". The listed defects: "the gauge field stores connection and curvature independently, the Lie algebra has no bracket, the Poincaré group is an arbitrary group unrelated to the Hamiltonian, and the "unbounded" physical Hamiltonian is tied to the spectrum of a bounded operator. The existence statement can therefore be satisfied by a two-dimensional toy model".

- No compiled witness exists for YM in their repository: `Tests/` contains nothing on Yang–Mills.
- "two-dimensional" is not made precise.
- The type `Spacetime := EuclideanCoordinateSpace ℝ 4` is fixed. The most plausible reading is therefore a two-dimensional Hilbert space, not a 2D space-time. The same construction was found independently for the luaartist derivative, see §1.5.

**Our diagnosis.** It is precise: each point refers to the code that was read.

- *Bounded operators on a real Hilbert space.* `OperatorValuedDistribution H := SchwartzSpace → (H →L[ℝ] H)` is an ARBITRARY function. It is neither linear nor continuous in the test function, and the operators are bounded. The Hamiltonian `hamiltonian : H →L[ℝ] H` is bounded, hence has compact spectrum. A genuine relativistic theory has unbounded fields and an unbounded H: true Yang–Mills does NOT satisfy this structure, and the "target" is ill-posed in both directions.
- *Freely given symmetries.* These are structure fields:
  - `poincare_group : Type` is arbitrary;
  - `time_reflection : SchwartzSpace → SchwartzSpace` is arbitrary, and the identity is allowed;
  - `euclidean_action` is arbitrary.

  "Reflection positivity" `0 ≤ S(fs.map θ ++ fs)` becomes trivial with θ = id and commuting symmetric operators.
- *Illusory classical link.* The Schwinger functions are moments of a classical (commutative) field, `∫ f ‖F_A‖²`, under an ARBITRARY measure on `GaugeField G`. The curvature there is a datum independent of the connection, and the σ-algebra is a free field as well.
- *Syntactic correspondence.* The correspondence with gauge-invariant polynomials is only an injection of a syntactic inductive type.
- *Weak cyclicity.* `field_generated_submodule` contains only the vectors `Φ(f)Ω`, without polynomials in the fields.

**Toy model, COMPILED** (a Lean file of about 630 lines, not included in this repository). It is built with Lean v4.31.0 against their exact definitions: declared dependency on the repository at commit `603053dc`, no copy; the checkout of the dependency is clean. Ingredients:
- `H = ℝ²` and a gauge measure with two atoms `½(δ_{A₁} + δ_{A₂})`;
- `A_k` has the single curvature `F₀₁ = √(w_k)·v`, where `w_k` is a smooth bump, the supports of w₁ and w₂ are disjoint, and v is a unit vector of the Lie algebra. The actions are equal (by translation);
- `Ω = (1/√2, 1/√2)` and `Φ(f) = diag(ν₁ f, ν₂ f)`, with `ν_k(f) = ∫ f w_k`;
- `H₀ = 1 − |Ω⟩⟨Ω|`, with spectrum `{0, 1}` (proved), hence gap 1 and mass 1;
- a trivial Poincaré group (`Unit`), `time_reflection = id`, `T_{μν} = 0`, and `op p = (enc p + 1)·Φ`, with an explicit injective encoding of the syntactic polynomials.

Theorems obtained:
- `LdWitness.fixedGroup_of_nontrivial`: `ClayYangMills.Formulations.FixedGroup G` for every `G` whose Lie algebra is non-zero;
- `LdWitness.lieAlgebra_nontrivial`: the Lie algebra of every instance of their class is non-zero. Otherwise the `LieGroup` model would have dimension 0, and G would be discrete and connected, hence trivial, which contradicts `non_abelian`;
- **`LdWitness.clayYangMills_holds : MillenniumYangMills.ClayYangMills`**.

All three depend only on `propext`, `Classical.choice`, `Quot.sound`. **The current "Clay" statement of lean-dojo is therefore a THEOREM**, satisfied by a toy model unrelated to Yang–Mills. This confirms, with a compiled witness, the claim of their README ("two-dimensional toy model": the dimension 2 is that of the Hilbert space). The copy from before their review, used by math-challenge.org, was on the contrary **uninhabitable** (§1.2): the two versions are invalid, in opposite directions.

### 1.2 math-challenge.org (repository lixiang90/math-challenge-millennium, Apache-2.0)

Workspace `generated/millennium_yang_mills`, Lean 4.32.2, read on 2026-10-25.

**Provenance.** The README says "adapted from lean-dojo/LeanMillenniumPrizeProblems at commit fd5207106c8c…", that is, 2026-07-11, BEFORE the September review. The competition target is `theorem clay_prize_yang_mills : ClayYangMills := by sorry`.

**Defect 1: contradictory vacuum axiom.** The `ChallengeDeps.lean` of this repository contains the vacuum axiom from before the review (line 1015):
```lean
vacuum_unique : ∀ Ω' : H, IsVacuum Ω' hamiltonian → (∀ g, unitary_rep g Ω' = Ω') → ‖Ω'‖ = 1 → Ω' = vacuum
```
- `−vacuum` is also normalised, invariant and of zero energy. The axiom therefore gives `−vacuum = vacuum`, hence `vacuum = 0`, which contradicts `‖vacuum‖ = 1`.
- The structure `QuantumYangMillsTheory G` is therefore EMPTY for every `G`.
- `ClayYangMills ≡ ∀ G [CompactSimpleGaugeGroup G], False` then asserts that no type admits an instance of a compact simple group. This is false mathematically, since SU(2) provides one, and therefore unprovable.
- The lean-dojo commit `1fdee4bc` (2026-09-07) itself says "the previous form was contradictory".

**COMPILED witness** (published in full in issue #2 of that repository: https://github.com/lixiang90/math-challenge-millennium/issues/2). It is built with Lean v4.32.2 against their exact definitions: declared dependency on the repository at commit `34dab7c7`, `ChallengeDeps.lean` with sha256 `5c3b0cc2…` identical to the file that was read, no copy. Results:
- `McWitness.wightman_inconsistent`: every `WightmanQuantumFieldTheoryProperties H Φ` of this copy implies `False`;
- `McWitness.quantumYangMillsTheory_isEmpty`: `IsEmpty (QuantumYangMillsTheory G)` for every `G`;
- `McWitness.clay_prize_iff_no_gauge_group`: `ClayYangMills ↔ ∀ G : Type, IsEmpty (CompactSimpleGaugeGroup G)`.

All three theorems depend only on `propext`, `Classical.choice`, `Quot.sound`. The competition target (`holes.json`: `theorem clay_prize_yang_mills : ClayYangMills`) is therefore equivalent to "there is no compact simple Lie group". The right-hand side is false mathematically (SU(2)), but this is not formalised in their class, which requires a smooth `LieGroup` model that Mathlib does not provide for SU(2).

**Defect 2: inverted locality direction.** The copy also has the old direction of the locality hypothesis, corrected in lean-dojo by PR #8.

**Caveat.** Their README says that the site's verifier rebuilds its files "independently". We can only vouch for the public copy.

### 1.3 google-deepmind/formal-conjectures (Apache-2.0)

The tree at HEAD (last push on 2026-10-24) contains `FormalConjectures/Millennium/{BSD,NavierStokes,Poincare,PvsNP,RiemannHypothesis}.lean`. There is **no Yang–Mills file**. `Wikipedia/Mills.lean` is about Mills' constant and is unrelated.

### 1.4 prove2me/formalpedia (Apache-2.0): the only serious statement

SHA `082b32d5`, Lean v4.33.1 environment. We read the files `Def_YMMG_YangMills.lean` and `Def_YMMG_Lattice.lean`. The file is dated 2026-09-25 and marked "**This is a proxy, and it needs review**".

**What it requires.**
- A complete `WightmanQFT`.
- A mass gap on the Wightman side.
- A SCALAR component that is "not a generalised free field".
- That its Schwinger functions be the scaling limit of Wilson's "plaquette action density" field, with `a → 0`, `aL → ∞`, `β → ∞`, and free `Z`, `c`.

**Convergence with this repository.** Its definitions of G and of the Wilson limit almost exactly coincide with ours: Lie algebra `{X | ∀t, exp(tX) ∈ ρ(G)}`, simplicity through ideals, action `β Σ (1 − Re tr ρ(U_p)/N)`, smeared Riemann sums. The two were written independently: `Group.lean` and `Lattice.lean` were written before formalpedia was read. This convergence suggests that these are the natural choices.

**Differences in fidelity.**

| Point | formalpedia | this repository |
|---|---|---|
| Framework | Wightman + Euclidean restriction | OS kernels + linear growth (reconstruction not formalised) |
| Field content | 1 scalar (action density) | 21 components of `Tr F_μνF_ρσ`, tensor representation of **O(4)** |
| Non-triviality | "not a generalised free field" | `m < ∞` + 21 non-zero components (A); UV fingerprint (B) |
| Sectors | the gap concerns the given QFT | `gap_all_sectors`: the same Δ for every extension by local observables (C-odd sectors) |
| Wilson representation | `∀ ρ` faithful (stronger than Clay) | `∃ ρ'` faithful (A) |
| Asymptotic freedom, tensor T | absent (said explicitly) | FP1–FP3 (κ imposed), T conserved and Ward-normalised, indecomposability (B, AB) |
| Compiled guards | none | 44 theorems (§4), second kernel nanoda, class of groups inhabited by SU(2) |

### 1.5 Other repositories

These repositories were surveyed in a separate AI agent run, which quoted the code verbatim through the GitHub API. formalpedia was re-read directly. For the others, the summaries below rest on that survey, checked only by reasoning about the quoted code. The commits are listed in §7.

- **consensusframework/yang-mills-mass-gap** (Apache-2.0, Lean and Mathlib v4.15.0). The open target `HasLatticeMassGap` requires `|corr(W, W∘translate^[k])| ≤ C e^{−mk}` for every `k` on a FINITE torus `Fin N`⁴. But `translate^[N] = id`, so the correlation is periodic in `k`; the bound forces a zero correlation, in particular `Var(W) = 0`. This is false for every non-degenerate model and trivially true for `χ ≡ 0`. The argument was checked: an N-periodic function bounded by `C e^{−mk}` is zero.
- **lluiseriksson/THE-ERIKSSON-PROGRAMME** (AGPL: read only). The former targets are vacuous (`∃ m_phys, 0 < m_phys`) or very probably uninhabitable. The current core contains no Clay statement, by the repository's own account.
- **jeffgurd888/thet-logos** (MIT, branch `master`). `ClayYangMills G := ∃ T, T.nontrivial ∧ HasMassGap T`, where `nontrivial : Prop` is a field chosen by the witness. This is vacuous: `⟨…, {0}, rfl, True⟩`.
- **luaartist/Yang-Mills-Lean-4-Scaffold-Archive** (PolyForm NC licence, no copy). It is derived from lean-dojo and admits the same two-dimensional toy model.
- **mrdouglasny/lgt** (Apache-2.0). A genuine decay theorem at strong coupling, `β < 1/(4n·maxNeighbors d)`, on a torus `(ℤ/N)^d` uniformly in N. This is not Clay: no limit `a → 0`, the regime opposite to `β → ∞`, and `U(n)` is not simple.
- **ColinBundschu/mass-gap**. Decidable arithmetic facts about Cartan tables, without group, field or space-time.
- **merfijang/yang-mills-gap**. An open lattice problem (SU(2), d = 4, uniform in L), not a Clay statement, and presented as such.
- **HEPLean/PhysLean → physlib**. Nothing on quantum YM, Wightman or OS.

## 2. Jaffe–Witten clauses ↔ Lean definitions

Quoted from the official problem description (https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf; text extracted with `pdftotext`).

| Clause (JW, quotation) | Lean definition | Comment |
|---|---|---|
| "for any compact simple gauge group G" (§4) | `CompactSimpleGroup` (`Group.lean`) | Compact, connected, Hausdorff group, with `ρ : G → U(N)` continuous and faithful and `𝔤_ρ = {X ∣ ∀t, exp(tX) ∈ ρ(G)}` simple. Excludes U(1) (proved), tori, finite groups and `SU(2)×SU(2)`. In B, simplicity is also reflected in `indecomposable`: no decoupled sectors, hence no product theory. |
| "a … quantum Yang–Mills theory exists on ℝ⁴" | `Schwinger YMIdx 4`, `Spacetime 4 := EuclideanSpace ℝ (Fin 4)` | The dimension is fixed by the type; nothing is left to the witness. |
| "axiomatic properties at least as strong as those cited in [45, 35]" ([45] Streater–Wightman, [35] OS 1973/1975) | `OSAxioms` (`OS.lean`): E0 smooth, E0' linear growth, E1 covariance under ℝ⁴ ⋊ **O(4)**, E2 reflection positivity, E3 symmetry, E4 cluster | Wightman follows from OS by the OS 1975 reconstruction theorem (not formalised). |
| "The Hamiltonian H … positive energy, 0 ≤ H, and a vacuum vector Ω … unique up to a phase" (§3) | in the Euclidean form of `HasMassGap` | `‖e^{−tH}(1−P_Ω)‖ ≤ e^{−Δt}` implies `H ≥ 0` and `ker H = ℂΩ`. |
| "A quantum field theory has a mass gap Δ if H has no spectrum in the interval (0, Δ) for some Δ > 0" (§4) | `HasMassGap R S Δ` (`Gap.lean`) | Decay `|⟪F,τ_t G⟫ − ⟪F,Ω⟫⟪Ω,G⟫| ≤ e^{−Δt}‖F‖‖G‖`, equivalent through OS reconstruction. |
| "The supremum of such Δ is the mass m, and we require m < ∞" | `FiniteMass` (`BddAbove {Δ ∣ HasMassGap Δ}`) | Excludes the trivial theory (proved). |
| "non-trivial" | A: `ComponentsNontrivial` + `FiniteMass`; B: `ComponentsNontrivial` + FP1 + `FiniteMass` + `indecomposable` | For composite fields, "non-Gaussian" is not enough (`:φ²:` is non-Gaussian). FP1 encodes the interaction (logarithms). |
| "local quantum field operators in correspondence with the gauge-invariant local polynomials in the curvature F and its covariant derivatives, such as Tr F_ij F_kl(x)"; footnote 1: "classical differential polynomials of dimension ≤ d does correspond to the space of local quantum operators of dimension ≤ d" | Indices `YMIdx = (Fin 4)⁴`, `tensorRep4`, `TensorSymmetric`; A: `gap_all_sectors` over EVERY gauge-invariant local observable | Dimension 4 explicit (21 components); higher dimensions only through the extension clause (A). |
| "Correlation functions … should agree at short distances with the predictions of asymptotic freedom"; "existence of a stress tensor and an operator product expansion" | B: `Conserved`, `WardEnergy`, `UVTrace` (FP1 with κ = 3 dim G/π⁴ imposed, FP2), `UVStress` (FP3) | OPE not formalised (see §6). |
| §6.5: "Wilson … lattice … gauge-invariant action … limits of appropriate expectations of gauge-invariant observables as the lattice spacing tends to zero and as the volume tends to infinity"; "Reflection positivity holds for the Wilson approximation" | A: `wilsonAction`, `latticeExpect`, `LatticeSeq` (a→0, (L+1)a→∞, β→∞), `LatticeConverges` | — |
| Footnote 2: "We specifically exclude weak-existence (compactness) … unless one also uses other techniques to establish properties of the limit (such as the existence of a mass gap and the axioms)" | A requires the properties of the limit: OS, gap, `m<∞` | A subsequence is allowed, in line with the footnote. |
| §5 (2): clustering `|⟨Ω,O(x)O(y)Ω⟩| ≤ e^{−C|x−y|}` for C < Δ | consequence of `HasMassGap` (not required separately) | — |

## 3. Design choices and fidelity risks

### 3.1 Schwinger kernels at non-coincident points (rather than a measure on S'(ℝ⁴))

**Why not a measure.** The local gauge-invariant fields of YM₄ have dimension ≥ 4 > d/2. They are not random distributions: already `:φ²:` of the free field in 4D has infinite variance, because `C(x)² ∼ |x|⁻⁴` is not locally integrable. The framework "measure on S'" (OS0–OS4 of Glimm–Jaffe, the one used for the free field in OSforGFF) suits the field φ, not composite fields.

**Choice made.** OS 1973 defines the Schwinger functions on °S, the test functions vanishing at the diagonals. For a reconstructible theory they are analytic off the diagonals. We therefore write them as functions `S : list of (index, point) → ℝ`; the values at coincident points are arbitrary and enter no axiom.

**Risk.** The pointwise bound `linear_growth` is a SUFFICIENT condition for E0' of OS 1975. We argue for it without proving it in Lean (Taylor expansion near the diagonals, order ∝ n). A theory that satisfied E0' without satisfying this bound would be wrongly excluded; we know of no relevant example.

### 3.2 Euclidean form of the gap

**Equivalence.** In the OS reconstruction, `⟪F, τ_t G⟫ = ⟨F, e^{−tH} G⟩` and `Ω = [vac]`. The condition `|⟪F,τ_t G⟫ − ⟪F,Ω⟫⟪Ω,G⟫| ≤ e^{−Δt}‖F‖‖G‖` on a dense set is equivalent to `‖e^{−tH}(1−P_Ω)‖ ≤ e^{−Δt}`, that is, to `spec(H|Ω^⊥) ⊂ [Δ, ∞)` (hence `ker H = ℂΩ`).

**Advantages.**
- No unbounded operator is handled in Lean; this was the defect that made the lean-dojo sketch ill-posed.
- No "Hamiltonian" datum is left free: H is defined by the correlations.

**Proved check.** `HasMassGap.mono`: the set of gaps is an interval.

### 3.3 Compact simple groups

**Encoding.** G is presented by a faithful continuous unitary representation (one always exists, by Peter–Weyl). `𝔤_ρ` is defined through the matrix exponential, and "simple" is stated without assuming that `𝔤_ρ` is a subalgebra, which holds mathematically.

**Lean risk: the junk exponential.** `NormedSpace.exp` would take the junk value `1` if `Algebra ℚ` were missing. Then `𝔤 = M_N(ℂ)`, which is not simple, the class would be EMPTY, and the three statements would be vacuously true (the "Hodge" lesson). **Risk excluded by proof** (`ClayYM/Inhabited/`):
- `SU2.lieAlgebra_eq`: for the inclusion SU(2) → U(2), `𝔤_ρ = su(2)`. The proof goes through a 2×2 Jacobi formula, `d/du det exp(uY) = tr Y · det exp(uY)`, and the uniqueness of the derivative at 0 of `u ↦ exp(uX)`;
- `SU2.isSimpleLieAlg_su2`: su(2) is simple;
- compactness of SU(2) (closed, bounded) and connectedness (image of S³);
- `compactSimpleGroup_nonempty` and `SU2.dim_eq_three`.

**Variant A.** The representation of the Wilson action is EXISTENTIAL (`∃ ρ'`). Imposing all faithful representations would be stronger than Clay, which fixes no regularisation.

### 3.4 Variant A: lattice limit

**Clauses** (`LatticeYMClauses`):
- OS;
- tensor symmetries;
- 21 non-zero components;
- convergence of the smeared correlations of the renormalised plaquette fields, `Φ = Z·Q − c`, with matrix mixing and subtraction of the identity;
- gap Δ and `m < ∞`;
- `gap_all_sectors`: the same Δ holds for every extension by continuous gauge-invariant local observables, treated as even scalars, as soon as the joint limit exists and satisfies OS.

**What A lets through, or risks:**
- *Universality.* The fidelity argument is the following. The only non-trivial gapped limits of the Wilson lattice of G (β → ∞) are YM_G: strong coupling ⇒ ξ_phys → 0 ⇒ trivial limit, rejected; β growing too fast ⇒ massless free gluons, rejected by the gap. This is the physics consensus, not a theorem.
- *Extensions.* `gap_all_sectors` uses a trivial representation on the new labels. This choice is SAFE: a mislabelled pseudo-scalar violates reflection positivity, hence the hypothesis; it can never demand a gap for a wrongly normed form. It covers the C-odd sectors through C-odd, P-even scalars (0⁺⁻) and their multipoint products.
- *Convergence.* It is smeared, with continuous compactly supported test functions off the diagonals and for `n ≥ 1`. A subsequence is allowed (JW, footnote 2).
- *Non-uniqueness.* Clay asks for existence, not uniqueness; the limit may depend on the subsequence.
- *More demanding than Clay on the method (review point B1).* A and AB require the theory to be a limit of the Wilson lattice, with an action and a renormalisation of fixed form (`Φ = Z·Q − c`). Clay fixes no route: a construction through another regularisation (another lattice action, a flow, stochastic quantisation) would satisfy A only by ALSO proving convergence of the Wilson lattice to it.
- *Less demanding than Clay on the field content (review point B2).* A imposes neither a stress tensor, nor asymptotic freedom, nor an OPE. `gap_all_sectors` is only an implication: if no joint extension converges, the clause is empty.

**Proved mutation test** (`trivial_wilson_limit`). For EVERY group, the trivial theory is a limit of the genuine Wilson measures (Z = 0). It satisfies OS, the tensor symmetries, convergence and the gap for every Δ, and it is rejected ONLY by `finite_mass` and `components_nontrivial`.

### 3.5 Variant B: axiomatic + fingerprint

**Field content.** The 21 components of `Tr F_μνF_ρσ`, in the tensor representation of **O(4)** (the full group: see θ below).

**Stress tensor.** `T_μν = z₁(Σ_ρ F_μρF_νρ − ¼δF²) + z₂ δF²`, with `z₁ ≠ 0` and two requirements:
- **conservation** at non-coincident points;
- **absolute normalisation by the Ward identity**: `d/dt⟪F,τ_t G⟫|₀ = ∫_{ℝ³} ⟪F, T₀₀(0,v⃗) G⟫_c d³v`. The sign and the scale are absorbed by `∃ z₁`.

In pure YM, the traceless part of T is proportional to the only symmetric traceless gauge-invariant operator of dimension 4, `(FF)^{tl}`. We prove `θ = Σ_μ T_μμ = 4 z₂ F²` (`θc_eq`).

**UV fingerprint.** The constants are checked by `constants/sympy_constantes.py`, whose expected output is `constants/constantes_verifiees.txt`.
- **FP1**: `|x|⁸⟨θ(x)θ(0)⟩_c (log|x|)² → κ`. θ is the trace anomaly (Collins–Duncan–Joglekar 1977): `θ = (β(g)/2g)F^aF^a` is invariant under the renormalisation group. Hence `|x|⁸⟨θθ⟩ = Φ(ḡ(1/|x|))`, with `Φ ∝ ḡ⁴` at leading order and `ḡ² ∼ 8π²/(b₀ ln(1/|x|Λ))`. b₀ cancels: κ = dim G·c_{F²}/16 = 3 dim G/π⁴, with `c_{F²} = 48/π⁴` computed by SymPy (sections 3 and 7a of the script). **Since the adversarial review, this value is IMPOSED** (`traceAnomalyCoeff`, proved > 0 through `CompactSimpleGroup.dim_pos`). Left free, it allowed the dimension to be completed with decoupled matter: see "What B lets through".
- **FP2**: `(|x|⁸⟨θθ⟩_c log²|x| / κ − 1)·L/ln L → −b₁/b₀² = −102/121`, with `L = −log|x|`. Two-loop coefficients: Caswell 1974, Jones 1974. The correction comes from `1/a = 2b₀L + (b₁/b₀) ln L + O(1)`. The script checks it numerically; the sequence (−0.944; −0.906; −0.883; −0.869; −0.863 for L = 10³…10¹⁶) converges to −0.843 like 1/ln L. This coefficient is independent of the scheme, of Λ and of the normalisation of θ. With the full factor `(β/2g)² = (b₀a + b₁a²)²/4` (section 7b), the sequence is −0.8330, −0.8399 and −0.8417 for L = 10⁵, 10¹⁶ and 10⁴⁰, identically for C_A = 2, 3 and 5.
- **FP3**: `s⁸⟨T_μν(su)T_ρσ(0)⟩_c → dim G · (4/π⁴) · ℐ_μν,ρσ(u)`. `4/π⁴ = 16/S₄²` is the C_T of a free Maxwell field, computed by Wick contractions in Feynman gauge. ℐ is the conformal structure (Osborn–Petkou 1994), checked in SymPy at 4 points and for 9 sets of indices.

**Indecomposability** (`indecomposable : ¬ Decomposable S`, added after the review). S is not the sum `indepSum S₁ S₂` of two independent fields, each being an OS theory (same representation `tensorRep4`) with a non-zero connected correlation (`HasConnected`).
- The formula is `indepSum S₁ S₂ (l) = Σ_{A ⊆ l} S₁(A) S₂(l∖A)`: these are the Schwinger functions of `O₁ ⊗ 1 + 1 ⊗ O₂` in the product vacuum.
- Proved checks: `indepSum_trivS_left` (a trivial factor gives back S) and `not_hasConnected_trivS`. Without the requirement `HasConnected`, every theory would be decomposable and B would be unsatisfiable.
- Proved mutation test (`uvFingerprint_indepSum`, through `conn2_indepSum`): connected functions add up, hence so do κ and C_T, and FP2 (a ratio) is unchanged. FP1–FP3 therefore cannot distinguish `YM_{G₁} ⊗ YM_{G₂}` from YM for a group of dimension `dim G₁ + dim G₂`. Examples of coincidences: 24 = 3 + 21 (SU(5) versus SU(2) × Spin(7)), 28 = 14 + 14 (Spin(8) versus G₂ × G₂).
- Proved guard: `indepSum_not_YMFingerprint`.
- Remark: every Gaussian theory with a reflection-positive covariance is decomposable (C = C/2 + C/2). This is consistent, since free theories are fake models.

**What B lets through:**
- **The group up to dim G, among simple groups.** Correlations of gauge operators normalised in a renormalisation-group-invariant way see h∨ = C_A only through `b₁/b₀² = 102/121`, proved universal (`b1_div_b0_sq`). In pure YM, the perturbative coefficients of gluonic operators are powers of C_A up to three loops. YM for Spin(7) and for Sp(6) (both of dimension 21; likewise for every pair B_n/C_n, n ≥ 3) are not separated.
  - One might hope to read h∨ through b₀; at this order and in these correlators, b₀ alone is not visible.
  - Reading h∨ would require an observable normalised through the connection, for example the gradient flow `t²⟨E(t)⟩ ∝ dim G/b₀`, which needs a gauge field: variant A, or AB.
- **The global form.** `SU(N)` and `SU(N)/ℤ_N` have the same local operators on ℝ⁴. This has no consequence for a statement that is "local on ℝ⁴".
- **The C-odd sectors** (SU(N≥3), Spin(4k+2), E6). The fields of dimension 4 are C-even; the gap of B covers only the sector they generate. B is therefore weaker than Clay for these groups; A corrects this point through `gap_all_sectors`.
- **θ ≠ 0** (topological term `iθQ`, imaginary in Euclidean signature). For θ ∉ {0, π}, two structural choices exclude it. On the one hand, the kernels are REAL (`Schwinger := … → ℝ`). On the other hand, the covariance concerns the FULL O(4), reflections included. For these θ, the mixed correlation `⟨F²(x) FF̃(0)⟩` is non-zero and imaginary; it is moreover forbidden by covariance under reflections (scalar × pseudo-scalar). This is an argument, not a Lean theorem.
  - θ = π is NOT excluded structurally: `(−1)^Q` is real and parity is preserved.
  - A mixed time-reversal / centre-symmetry anomaly (Gaiotto–Kapustin–Komargodski–Seiberg, JHEP 05 (2017) 091, doi:10.1007/JHEP05(2017)091; metadata checked, the article was not re-read for this document, content reported) forbids a trivial phase, that is, one with a gap, a unique vacuum and preserved symmetries. Three options remain: broken CP (degenerate vacua), no gap, or a topological phase (TQFT). The first two are rejected by `HasMassGap`. The third would NOT be rejected by a framework restricted to local operators: this is a residual loophole of B at θ = π.
  - Variant A excludes every θ ≠ 0 by construction, since the Wilson action has no θ term.
- **Matter.** An earlier formulation claimed that matter was "rejected by FP2/FP3". This was INCORRECT for decoupled matter (review point A1).
  - Decoupled free matter does not change b₁/b₀², and FP3 is additive: `YM_SU(2)` + 12(dim G − 3) massive free scalars (C_T of a scalar = 1/(3π⁴), that is, one gluon for 12 scalars) had exactly the C_T of dim G gluons.
  - It is now rejected in two ways. By FP1, since κ is imposed: free massive matter does not contribute to the logarithm, so κ = 9/π⁴ ≠ 3 dim G/π⁴; this is an argument, not formalised. And by `indecomposable`: proved rejection as soon as the factors are OS theories (`indepSum_not_YMFingerprint`).
  - Charged matter (QCD, SYM) is not decoupled. The argument is then the following: κ depends only on the number of gauge bosons (b₀ cancels), so FP1 fixes `dim G' = dim G`; the matter then adds to C_T (FP3) and changes b₁/b₀² (FP2). This is an argument, not proved.
- **The cost of indecomposability.** It is implicit in JW ("YM for a simple G"), but not written. A witness would have to prove that its theory is not a decoupled sum, which is a universal statement about S₁ and S₂. That it holds for YM_G (interacting glueballs, non-factorised local algebra) is a physical belief, with the same status as FP1–FP3.

**Proved mutation test** (`freeGluons_mutation`). The "free gluons" structure (dim G Maxwell fields, exactly conformal `⟨TT⟩`) SATISFIES FP3 but violates FP1: FP1 is the clause that encodes the interaction.

### 3.6 Variant AB

`LatticeYMClauses ∧ YMFingerprint`. It is the strongest and the most faithful, and it is **the recommended reference statement** (conclusion of the adversarial review):
- G is constructed by the lattice, which removes the "up to dim G" ambiguity of B;
- the tensor T, the UV fingerprint and indecomposability are imposed, which fills the gap in field content of A (B2).

On the other hand it inherits the "Wilson route" requirement of A (B1): it therefore asks more than Clay about the method. Proved: `ClayYM_AB.toA` and `ClayYM_AB.toB`.

## 4. Fake models: table

| Fake model | Clause that rejects it | Lean proof | Theorems (`ClayYM.*`) |
|---|---|---|---|
| Trivial theory (H = ℂΩ) | `FiniteMass` (m < ∞); in A also `ComponentsNontrivial`; in B also FP1 | **yes** | `trivS_OSAxioms` (satisfies OS!), `trivS_hasMassGap` (every Δ), `trivS_not_finiteMass`, `trivS_not_clayMassGap`, `trivS_not_ComponentsNontrivial`, `trivS_not_UVTrace`, `trivS_not_YMFingerprint`, `trivS_not_B`; also satisfies `TensorSymmetric`, `Conserved`, `WardEnergy` |
| Trivial limit of the genuine Wilson measures (Z = 0; or strong coupling, ξ_phys → 0) | `finite_mass`, `components_nontrivial` (A) | **yes** | `trivial_wilson_limit` (satisfies every other clause on the limit theory) |
| 2D Yang–Mills | type (d = 4 imposed) + trivial local sector ⇒ `FiniteMass` | **yes** for the part generic in d; the fact "trivial local sector" is cited (Driver 1989, Gross–King–Sengupta 1989: curvature = white noise in axial gauge), not formalised | `ym2d_local_sector_not_finiteMass`, `ym2d_local_sector_OS` |
| Massive free scalar field (every mass m) labelled "SU(2)" | FP1 (`UVTrace`); in A: impossible by construction | **yes** for θ = any Wick polynomial without derivatives. The bounds `c₁/|x|² ≤ C_m(x) ≤ c₂/|x|²` (0 < \|x\| ≤ 1) are PROVED for the proper-time kernel `C_m(x) = ∫₀^∞ (4πs)⁻² e^{−|x|²/4s − m²s} ds`. The Wick identity `⟨θθ⟩_c = Σ w_k² k! C^k` is not formalised (checked by enumeration for k ≤ 6) | `wick_not_UVTrace`, `gffKernel_lower`, `gffKernel_upper`, `gff_wick_not_UVTrace` |
| Free gluons (dim G Maxwell fields, YM at g = 0) | FP1 (θ ≡ 0); gap (massless) | **yes** (FP1); gap: no | `freeGluons_mutation` (passes FP3 and fails FP1), `exactConformal_not_UVTrace`, `freeGluons_not_fingerprint_with` |
| Every CFT (θ ≡ 0) | FP1 | **yes** | `not_UVTrace_of_zero` |
| Massive free vector field (Proca), dim G copies | FP1 (`θ = −m²A²`: `|x|⁸⟨θθ⟩ → const > 0`, because the longitudinal mode dominates); FP3 (C_T of Proca ≠ Maxwell) | **no**: the obstruction lemma `not_UVTrace_of_lower_bound` applies, but the lower bound on the second derivatives of C_m is not formalised | — |
| U(1) (Maxwell), every group with a faithful representation of dimension ≤ 1 | class of groups (simplicity) | **yes** | `not_simple_dim_one`, `CompactSimpleGroup.two_le_N` |
| POSITIVE control: SU(2) | must BELONG to the class of groups | **yes** (it belongs) | `compactSimpleGroup_nonempty`, `SU2.lieAlgebra_eq`, `SU2.isSimpleLieAlg_su2`, `SU2.dim_eq_three` |
| YM_SU(2) ⊗ 12(dim G − 3) decoupled massive free scalars (counterexample A1 of the review against the former B) | `indecomposable`; FP1 since κ is imposed | **yes** through `indecomposable`, as soon as both factors are OS; FP1: argument | `indepSum_not_YMFingerprint`, `conn2_indepSum` |
| Products `YM_{G₁} ⊗ YM_{G₂}` with dim G₁ + dim G₂ = dim G (for example SU(2) × Spin(7) for SU(5)) | `indecomposable` ONLY: FP1–FP3 do not reject them (proved) | **yes** | `uvFingerprint_indepSum` (passes FP1–FP3), `indepSum_not_YMFingerprint`; checks `indepSum_trivS_left`, `not_hasConnected_trivS` |
| YM for another SIMPLE group of the same dimension (Spin(7)/Sp(6)) | not rejected by B; rejected by A and AB (construction) | n/a | loophole of B documented (§3.5) |
| YM at θ ∉ {0, π} | real kernels + full O(4) (`⟨F²·FF̃⟩` would be imaginary and non-zero); in A: by construction | no (argument) | — |
| YM at θ = π | B: only if CP is broken or if there is no gap (GKKS anomaly); a TQFT phase would NOT be rejected by B; A: rejected by construction | no (argument) | — |
| QCD / YM + asymptotically free charged matter | FP1 (κ fixes dim G) then FP3 (excess C_T); FP2 (b₁/b₀²) | no (argument) | `b1_div_b0_sq` (universality proved), `traceAnomalyCoeff_pos` |
| Massless Gaussian limit (β_k growing too fast) | mass gap | no (argument) | — |

Reusable obstruction lemmas (proved):
- `not_UVTrace_of_lower_bound`: `|x|⁸⟨θθ⟩ ≥ c > 0`, hence no logarithm;
- `not_UVTrace_of_upper_bound`: `≤ C|x|^α`;
- `not_UVTrace_of_zero`;
- `confI_traceless`;
- `conn2_θc` (bilinearity);
- `conn2_indepSum` (additivity of connected functions under a decoupled sum), `UVTrace_indepSum`, `UVStress_indepSum`.

## 5. Comparison with the version judged invalid (lean-dojo)

| lean-dojo defect | Treatment here |
|---|---|
| connection and curvature stored independently; arbitrary measure on fields (A, F) | A: link configurations `U : links → G`, plaquettes computed from U, product Haar measure × e^{−S} imposed. B: no classical data at all; only kernels, constrained by OS, Ward and the fingerprint |
| Lie algebra without a bracket | `𝔤_ρ` defined by `exp` in `M_N(ℂ)`, bracket = matrix commutator, simplicity through ideals |
| arbitrary Poincaré group, unrelated to H | CONCRETE Euclidean group `ℝ⁴ ⋊ O(4)` (`Spacetime 4 ≃ₗᵢ[ℝ] Spacetime 4`), concrete reflection θ; H defined by the correlations (`τ_t`) |
| bounded Hamiltonian, spectrum of a bounded operator | no operator: gap in Euclidean form, equivalent to the spectrum of the unbounded H through OS reconstruction |
| free `time_reflection`, `euclidean_action`; trivial RP | reflection θ fixed (`ClayYM.θ`), action on the components through `tensorRep4 (θ 4)` |
| operator values = arbitrary functions | kernels smooth off the diagonals + linear growth |
| invariant polynomials = syntactic type, injection | 21 physical components with symmetries and O(4) representation; A: all gauge-invariant local observables (`gap_all_sectors`) |
| contradictory vacuum axiom (before 09/2026) | non-contradictory OS axiom system: the trivial theory satisfies it (`trivS_OSAxioms`) |
| "satisfiable by a 2D toy model" (without a compiled witness in their repository; compiled for this work: `LdWitness.clayYangMills_holds`, not included here) | no datum left to the witness; compiled fake models (§4); mutation tests |

## 6. Honest limitations

1. **OS reconstruction not formalised.** That `OSAxioms` implies Wightman, and that `HasMassGap` is equivalent to the spectral condition on H, rests on the OS 1975 theorem and on a standard spectral argument, not formalised. The pointwise growth bound is an argued sufficient condition, not proved.
2. **"This is Yang–Mills for G".**
   - A: faithful modulo the universality of lattice limits, which is a physical belief.
   - B: faithful up to `dim G` among simple groups (§3.5), and only after the two fixes of the review (κ imposed, `indecomposable`). Before these fixes, B reduced to SU(2). The fingerprint has only the leading and the first subleading order, without a full OPE.
   - AB: recommended reference statement (§3.6).
   - Correspondence with ALL invariant polynomials: explicit in dimension 4 only; beyond, only through `gap_all_sectors` (A).
3. **Physical constants.** FP1–FP3 are perturbative predictions, which Clay explicitly demands ("agree at short distances with the predictions of asymptotic freedom"). If a constant were wrong, statement B would be FALSE for true YM.
   - Measures taken: FP2 is a dimensionless ratio; FP3 is computed by SymPy from Wick contractions and cross-checked with the Osborn–Petkou structure.
   - κ is now IMPOSED (3 dim G/π⁴). This strengthens B, but makes the statement sensitive to an error in `c_{F²}` or in the Ward normalisation. Double check: SymPy (sections 3 and 7a) and a separate re-derivation by an AI reviewer instance (not an independent human check). That run also reported a numerical check of the Ward normalisation (ratio 1.0000000000000004), of the reflection signs and of the absence of vacuity through junk values; that computation is not archived in this repository.
   - An independent human audit of these three clauses remains necessary. As T. Hales puts it in a guest post on T. Tao's blog (2026-10-09), "a proof in Lean should not be accepted until a human audit is performed to ensure statement fidelity."
4. **Incomplete guards.**
   - The GFF fake model is rejected only for θ a Wick polynomial WITHOUT derivatives, and the Wick identity is not formalised.
   - Proca, θ ≠ 0, charged and massless matter are only argued.
   - Decoupled sums are rejected in Lean only through `indecomposable`; the rejection of decoupled free matter through FP1 (κ imposed) is argued.
   - The models are not constructed as complete OS theories in Lean: the guards have the form "every theory whose two-point function equals X violates clause Y", which is stronger than a single instance. Only the trivial theory is constructed, and it satisfies all the OS axioms.
5. **Non-vacuity.**
   - The class of groups is inhabited: SU(2), proved.
   - The system "OS axioms + gap" is consistent: the trivial theory satisfies it, proved.
   - The consistency of the COMPLETE statement (non-triviality, fingerprint) is precisely the open problem.
6. **Trust base.**
   - No project axiom.
   - Lean v4.34.0 (released on 2026-09-14), later than v4.33.1 (2026-08-21), the release that according to L. de Moura's postmortem (2026-08-24) fixed all the issues found during the summer-2026 kernel soundness bug hunt.
   - Second, independent kernel nanoda 0.4.19, without the Lean runtime or GMP: 51 133 declarations without error; axioms = the three standard ones; negative witness (`1 = 2` by `sorry`) rejected. This check was run locally and is not part of `scripts/verify.sh`.
   - Rebuild from a clean copy of the sources: green (see `README.md`).
7. **External witnesses.**
   - The witness against math-challenge.org (Lean 4.32.2) and the witness against lean-dojo (Lean 4.31.0) were checked with the toolchains pinned by those repositories, by `#print axioms` and `leanchecker` (without `--fresh`) only; they were not passed through nanoda, for lack of `lean4export` for those versions.
   - These two versions predate part of the 2026 kernel fixes. Those flaws can only be exploited by adversarial meta-programs, and these proofs are ordinary proofs without `native_decide`; the residual risk is small but not zero.
8. **No third-party code.** Dependencies are declared through the manifest; no third-party code is copied.
9. **Departures from Clay found by the adversarial review** (in addition to A1, fixed):
   - B1: A and AB require the Wilson route (§3.4);
   - B2: A requires neither T, nor asymptotic freedom, nor an OPE, and `gap_all_sectors` is an implication;
   - B3: in B, the gap concerns only the C-even sector generated by the 21 components;
   - C1: the pointwise linear growth is stronger than the distributional E0' (§3.1);
   - C2: `minDist⁻¹ = 0` for n ≤ 1, without consequence;
   - C3: the pointwise cluster property is stronger than E4, but it holds in the presence of a gap;
   - C4: the junk value of `log(−log‖x‖)` at ‖x‖ = e⁻¹ is without consequence, since the limits at 0 only see small ‖x‖.

## 7. References (checked)

- A. Jaffe, E. Witten, *Quantum Yang–Mills Theory* (official Clay problem description), https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf.
- K. Osterwalder, R. Schrader, *Axioms for Euclidean Green's functions*, Commun. Math. Phys. **31** (1973) 83–112, doi:10.1007/BF01645738; *Axioms for Euclidean Green's functions II*, Commun. Math. Phys. **42** (1975) 281–305, doi:10.1007/BF01608978 (references [35] of JW).
- R. Streater, A. Wightman, *PCT, Spin and Statistics, and All That* (1964) (reference [45] of JW).
- K. Osterwalder, E. Seiler, *Gauge field theories on a lattice*, Ann. Phys. **110** (1978) 440–471, doi:10.1016/0003-4916(78)90039-8.
- H. Osborn, A. Petkou, *Implications of Conformal Invariance in Field Theories for General Dimensions*, Ann. Phys. **231** (1994) 311–362, doi:10.1006/aphy.1994.1045, arXiv:hep-th/9307010.
- J. C. Collins, A. Duncan, S. D. Joglekar, *Trace and dilatation anomalies in gauge theories*, Phys. Rev. D **16** (1977) 438–449, doi:10.1103/PhysRevD.16.438.
- W. E. Caswell, Phys. Rev. Lett. **33** (1974) 244–246, doi:10.1103/PhysRevLett.33.244; D. R. T. Jones, Nucl. Phys. B **75** (1974) 531–538, doi:10.1016/0550-3213(74)90093-5.
- D. Gaiotto, A. Kapustin, Z. Komargodski, N. Seiberg, *Theta, time reversal and temperature*, JHEP **05** (2017) 091, doi:10.1007/JHEP05(2017)091.
- B. K. Driver, *YM₂: continuum expectations, lattice convergence, and lassos*, Commun. Math. Phys. **123** (1989) 575–616, doi:10.1007/BF01218586; L. Gross, C. King, A. Sengupta, *Two dimensional Yang–Mills theory via stochastic differential equations*, Ann. Phys. **194** (1989) 65–112, doi:10.1016/0003-4916(89)90032-8. Titles and metadata checked with Crossref; the content "curvature = white noise in axial gauge" is reported, the articles were not re-read for this document.
- T. Hales, *What mathematicians should know about the Lean Theorem Prover: questions of reliability and AI*, guest post on T. Tao's blog, 2026-10-09, https://terrytao.wordpress.com/2026/10/09/what-mathematicians-should-know-about-the-lean-theorem-proverquestions-of-reliability-and-ai/.
- L. de Moura, *Postmortem for the Kernel Soundness Bug Hunt*, 2026-08-24, https://leodemoura.github.io/blog/2026-8-24-postmortem-for-the-kernel-soundness-bug-hunt/.
- Repositories (read through the GitHub API on 2026-10-25):
  - lean-dojo/LeanMillenniumPrizeProblems @ `603053dc267cf3efe422f438eb78098c0ececd6f`;
  - lixiang90/math-challenge-millennium @ `34dab7c7f3bb0405d0092118bde9e14f10861cdd`;
  - google-deepmind/formal-conjectures (HEAD pushed on 2026-10-24);
  - prove2me/formalpedia @ `082b32d5d4099d88e510efc822346b699a9584fa`;
  - other surveyed repositories (§1.5), commits as recorded by the survey: consensusframework/yang-mills-mass-gap @ `2ef6500d`, lluiseriksson/THE-ERIKSSON-PROGRAMME @ `f5a8552c`, jeffgurd888/thet-logos @ `0415a181` (branch `master` @ `43f06180`), luaartist/Yang-Mills-Lean-4-Scaffold-Archive @ `d49de97c`, mrdouglasny/lgt @ `b8793ccf`, ColinBundschu/mass-gap @ `9a93f328`, merfijang/yang-mills-gap @ `eedf1ece`, leanprover-community/physlib @ `8ddcc004`.
