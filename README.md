# KarcherIndex

A Lean 4 formalization of the Morse index and nullity of Karcher saddle towers.

The project formalizes results from the preprint
[*Morse index of Karcher saddle towers in ℝ² × S¹(m)*](https://arxiv.org/abs/2608.13451v2).
The development connects
explicit Enneper–Weierstrass data, geometric quotients, disk and circle problems,
and certified bounds on the threshold α\*.

## Main results

The five compared statements are in
[`Palomar/CombinedChallenge.lean`](Palomar/CombinedChallenge.lean), in namespace
`KSPalomar.Intrinsic.Full`. Their proofs are re-exported by
[`Palomar/Solution.lean`](Palomar/Solution.lean).

| Compared declaration | Mathematical statement |
|---|---|
| `exists_intrinsic_index_nullity_m2` | For every k ≥ 3, there exists an Enneper–Weierstrass realization of the two-period quotient with index 4k − 3 and bounded Jacobi-field nullity 3. |
| `exists_intrinsic_staircase_k3` | For k = 3, one base realization and one threshold serve all positive periods, with compatible quotient witnesses having index 6m − 4⌊mα\*⌋ − 3 and nullity 7 at integral mα\*, and 3 otherwise. |
| `unique_threshold` | Exactly one real parameter s satisfies the spectral sign characterization `IsThreshold`. |
| `decimal_bounds` | Every such s gives 0.4323617 < `criticalPhase s` < 0.4323619. |
| `period_arithmetic` | For 0 < m ≤ 2298, the floor of m times the critical phase is ⌊4323617m / 10000000⌋, and m times the critical phase is not an integer. |

Here α\* denotes `criticalPhase s` for the unique parameter satisfying
`IsThreshold`. The Solution identifies that parameter with
`KsIndex.Staircase.sstar`; its critical phase is the library's
`KsIndex.Staircase.alphaStar`. The geometric and numerical results therefore use
the same threshold. The [definition review guide](DEFINITION_REVIEW_GUIDE.txt)
gives a reading order through these statements and their definitions.

The supporting library provides the following formulations and consequences.

The geometric statements are in
[`KarcherGeometricCapstone.lean`](KsIndexLean/KarcherGeometricCapstone.lean).
They use complex test spaces and complex bounded Jacobi fields; the precise
carriers and invariants are defined in
[`KarcherGeometricInvariants.lean`](KsIndexLean/KarcherGeometricInvariants.lean).
The existence theorems construct realizations from the Enneper-Weierstrass data.

For the two-period quotient Ξ_{k,2}, with k ≥ 3:

- `geometricIndex_two` gives index 4k − 3.
- `geometricNullity_two` gives nullity 3.

For the six-ended family Ξ_{3,m}, with positive integer m:

- `geometricIndex_three` gives index 6m − 4⌊mα\*⌋ − 3.
- `geometricNullity_three` gives nullity 7 when mα\* is an integer, and 3 otherwise.

The threshold α\* is `KsIndex.Staircase.alphaStar`. The qualitative theory proves
1/3 < α\* < 1/2. Separate numerical certificates prove the strict interval

**0.4323617 < α\* < 0.4323619.**

The lower endpoint is
[`alphaStar_gt_4323617`](KsIndexLean/AlphaRemarkLowerCertified.lean)
(in namespace `KsIndex.AlphaRemarkTrial.LowerAssembly`); the upper endpoint is
[`NegSignProd.alphaStar_lt_upper_decimal`](KsIndexLean/NegSignDecimal.lean).
The combined submission includes both numerical certificate stacks.

For every positive m ≤ 2298, the certified interval also gives
⌊mα\*⌋ = ⌊4323617m / 10000000⌋ and proves that mα\* is not an integer.
Consequently, the six-ended quotient has index
6m − 4⌊4323617m / 10000000⌋ − 3 and nullity 3. These arithmetic and geometric
consequences are provided by `AlphaStarNumericalPeriods` and
`KarcherNumericalPeriods`.

[`KarcherSmallPeriods.lean`](KsIndexLean/KarcherSmallPeriods.lean) proves the
introductory corollary for m = 1, 2, 3, 4, 6: the respective indices are
3, 9, 11, 17, 25, and every nullity is 3. This corollary uses the qualitative
threshold bounds and does not import the numerical certificate stacks.

## Guide to the development

| Topic | Entry points |
|---|---|
| Geometric invariants and final formulas | [KarcherGeometricInvariants](KsIndexLean/KarcherGeometricInvariants.lean), [KarcherGeometricCapstone](KsIndexLean/KarcherGeometricCapstone.lean) |
| Circle threshold and index/nullity dictionary | [Statements](KsIndexLean/Statements.lean), [Staircase](KsIndexLean/Staircase.lean) |
| Single-arc index theorem | [ArcMain](KsIndexLean/ArcMain.lean) |
| Dirichlet-to-Neumann circle operator | [DtNCircle](KsIndexLean/DtNCircle.lean) |
| Half-period Dirichlet and Neumann counts | [KarcherHalfPeriodTotalIndex](KsIndexLean/KarcherHalfPeriodTotalIndex.lean), [KarcherHalfPeriodTotalNullity](KsIndexLean/KarcherHalfPeriodTotalNullity.lean) |
| Hemisphere Jacobi extension and full test duality | [HemisphereJacobiExtension](KsIndexLean/HemisphereJacobiExtension.lean), [JacobiExtensionFullDuality](KsIndexLean/JacobiExtensionFullDuality.lean) |
| Rational phase index and bounded-field nullity | [KarcherRationalPhaseCounts](KsIndexLean/KarcherRationalPhaseCounts.lean) |
| Selected principal declarations and their axioms | [Inventory](KsIndexLean/Inventory.lean) |

For the six-ended family, the phase results retain threshold equality cases:
interior phases have index
6 inside (α\*, 1 − α\*) and 4 outside it, including its endpoints; their
bounded-field nullity is 2 at the endpoints and 0 elsewhere. The rational-phase
wrapper uses the reduced denominator to select the quotient.

## Scope and fidelity

The paper describes α\* = 0.4323618(1) as a heuristic numerical computation.
This formalization proves the strict decimal enclosure and its finite-period
arithmetic consequences; it does not merely assume the numerical estimate.

This is not a claim that every statement or argument in the paper has been
formalized. In particular, the development does not assert surface uniqueness,
a general topological genus identification, or the proposed geometric
interpretations of the exceptional ODE solutions. The retained cellular/Euler
characteristic certificates do not by themselves identify the genus of the
geometric quotient. Standalone completeness and asymptotic classification, and
half-period graphicality, are outside the stated scope.

The class-zero mixed-boundary index and nullity follow the paper's strict
Dirichlet–mixed–Neumann eigenvalue bracketing argument. The main two-period index
proof uses this route; the constructive Gram-matrix proof remains available as
an alternative. In the checkerboard containment statement of Theorem 1.1(v)
of arXiv:2608.13451v2, the printed r > 0 should be replaced by r ≥ 0.
Fidelity claims must retain this endpoint correction. Neither the numerical
interval nor the nullity dichotomy establishes irrationality of α\*.

For the six-ended family and rotational
character `j ≡ 2 mod 3`, the geometric screw acts on the lower-trace Fourier
coefficients by `exp(iπ(α + 2/3))` times the circle involution. This identification
is proved for bounded geometric Jacobi joint fibers and compact smooth geometric
joint-sector tests on finite period quotients, with rational phase `α = n/m`.
See [KarcherScrewJacobiTransport](KsIndexLean/KarcherScrewJacobiTransport.lean)
and [KarcherScrewSmoothTransport](KsIndexLean/KarcherScrewSmoothTransport.lean).

## Combined submission

[`CombinedChallenge.lean`](Palomar/CombinedChallenge.lean) gives the geometric
objects, the spectral characterization of the critical phase, and five statements.
The geometric staircase and numerical bounds use the same threshold definitions.
The statement includes threshold uniqueness and the arithmetic consequences through
period 2298; it does not assert irrationality.

[`Solution.lean`](Palomar/Solution.lean) publicly re-exports the five proofs from
[`CombinedSolution.lean`](Palomar/CombinedSolution.lean).
[`comparator.json`](comparator.json) selects exactly these five results.
The project metadata is in [`formalization.yaml`](formalization.yaml).

## Building

The toolchain is pinned to `leanprover/lean4:v4.35.0-rc3` in
[`lean-toolchain`](lean-toolchain). Mathlib and Tau Ceti revisions are fixed by
[`lake-manifest.json`](lake-manifest.json) and [`lakefile.toml`](lakefile.toml).
The Lean package and module namespace remain `KsIndexLean`.
With `elan` installed and the pinned dependencies available:

```sh
lake build KsIndexLean PalomarCombined
lake comparator --config comparator.json
```

The combined target includes the numerical proofs. A clean build and the complete
comparator can require substantial time and memory. The default target is
`PalomarCombined`; building it checks its imported proof dependencies. The explicit
`KsIndexLean` target above additionally builds every library source module, including
supporting results outside the five selected proofs.

Optional checks, certificate generators, and finite diagnostics are described in
[the scripts guide](scripts/README.md). They supplement the workflow above.

## Verification and trust

The five Challenge statements deliberately contain `sorry` placeholders. Their
Solution proofs use only `propext`, `Classical.choice`, and `Quot.sound`, as checked
by a local axiom audit. These statement placeholders are excluded from the
metadata's proof-development `sorry` counts.

The numerical proofs use optimized certificate representations and compilation
ordering while preserving all five selected results, including the same strict
decimal bounds and arithmetic consequences through period 2298. The selected
proofs have passed statement comparison, the permitted-axiom check, and independent
checking by Lean's default kernel and NanoDa.

A fresh-session Claude Opus 5.5 source review examined public commit `97b6d52`.
A follow-up at `98ac7ef` checked the revised mathematical documentation and
confirmed that the intervening Lean changes were comment-only. At that commit,
the reviewer reported no changes required before submission. These reviews used
source reading and scripted checks; neither included a build or Comparator run.
Their findings apply to those commits and the changes examined, rather than to
later revisions. The reviewer belongs to the same model family as earlier Claude
collaborators.

We thank Claude Opus 5.5 for a fresh-session source review and follow-up that
improved the mathematical exposition and clarified the scope of the formalization.

## Contributors

David Wiygul initiated and directed the formalization and reviewed mathematical
statements and design decisions. Development and review have involved the AI
collaborators Claude Opus 4.8 and Claude Fable 5 (Anthropic) and GPT-6 Astra
(OpenAI); the Claude collaboration continues the one acknowledged in the mathematical
paper. Selected self-contained lemmas were produced with
Aristotle (Harmonic) and checked in
the project's Lean environment. Mathematical attribution and proof-route
information belong with the relevant declarations and modules. Historical
Aristotle job records and the scope of verification are documented in
[the submission metadata](formalization.yaml).

## License

Apache-2.0; see [LICENSE](LICENSE).
