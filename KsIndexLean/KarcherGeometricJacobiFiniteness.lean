module

public import KsIndexLean.GammaEndProducerGeneralK
public import KsIndexLean.Caccioppoli
public import KsIndexLean.KarcherSmoothFunctionTransport
public import KsIndexLean.KarcherCopyJacobi
public import KsIndexLean.KarcherJacobiForward
public import KsIndexLean.KarcherQuotientJacobiOperator
public import KsIndexLean.KarcherQuotientDirichlet
public import KsIndexLean.KarcherEnergyIntegrability
public import KsIndexLean.KarcherDiskEncoding
public import KsIndexLean.KarcherFiniteDiskCopies
public import KsIndexLean.KarcherDiskFunctions

@[expose] public section


/-!
# Geometric `jacobi_finiteness` on the actual EW quotient

The paper's `jacobi_finiteness` (ksindexi.tex:1166) is the equivalence, for
`k ≥ 3`, `m ≥ 1`,

> a smooth geometric Jacobi field on `Ξ_{k,m}` is bounded ⟺ it has finite
> Dirichlet (gradient) energy `‖du‖²_{L²(g_k)}`.

This file realizes **both** directions on the *actual* EW period quotient
`PaperHalfPeriodRealization` (distinct from the chain carrier on which the
underlying bounded ⟷ finite-energy theorems are proved), for all `k ≥ 2`
(strengthening the paper's `k ≥ 3`), and assembles the full iff
`geometric_jacobi_finiteness`.  Both directions use the hypothesis exactly as the
paper states it — no auxiliary value-`L²` premise.

* `geometric_jacobi_finiteness_reverse` (⇐): finite quotient-area Dirichlet
  energy ⟹ bounded.  Consumes `bounded_of_jacobi_gradEnergySmooth`, the general-`k`
  finite-gradient-energy boundedness theorem on the chain carrier (the gradient
  carrier `GradEnergySmooth` is what drops the value-`L²` premise).
* `geometric_jacobi_finiteness_forward` (⇒): bounded ⟹ finite energy.  Consumes
  the Caccioppoli inclusion `bddJacobi_le_energySmooth`.

Both pass through the same encoding `e := encodeDiskFunction (R.diskFunctionPullback G)`
and the same transport lemmas (`contMDiff_iff_isSmooth_encoding`,
`encoding_isJacobiField_iff_openCopies` fed by `isGeometricJacobi_iff`,
`encodeDiskFunction_{punctureZero,seamVal}`), the actual-vs-flat Dirichlet identity
`lintegral_quotientGradSq_eq_flat`, and the exterior-vanishing of `gradSq e`, so the
quotient-area integral and the flat per-copy energy sum are interchangeable.  The
reverse descends the bound to `G` via `orderedDiskPoint_surjective` and the value
identity `encodeDiskFunction_on_disk`; the forward packages the hypotheses as a
`boundedGeometricJacobi` and encodes it with `boundedGeometricJacobi_encoding_mem`.
Every sub-piece is boundedness-free where the reverse needs it, so the boundedness
conclusion is genuinely *granted*, not assumed.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Manifold ContDiff
open KsIndex.FaithfulInjection

namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open scoped ParameterAtlas

variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

/-- **Geometric `jacobi_finiteness` (⇐), on the actual EW quotient.** A smooth
geometric Jacobi field `G` on `Ξ_{k,m}` with finite quotient-area Dirichlet
energy is bounded (`k ≥ 2`). Carries the general-`k` finite-gradient-energy
boundedness theorem `bounded_of_jacobi_gradEnergySmooth` from the chain carrier
to the surface. -/
theorem geometric_jacobi_finiteness_reverse (R : PaperHalfPeriodRealization k)
    (G : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (hsm : letI := HeightLift.periodChartedSpace R.hC m
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G)
    (hjac : R.IsGeometricJacobi G)
    (henergy : ∫⁻ q, ENNReal.ofReal (R.quotientGradSq G q) ∂(R.quotientArea) ≠ ⊤) :
    ∃ C : ℝ, ∀ q, ‖G q‖ ≤ C := by
  have hk : 2 ≤ k := h.out
  -- Step 1: the canonical encoding is a smooth disk family.
  have hsmooth : Surface.IsSmooth k m (encodeDiskFunction (R.diskFunctionPullback G)) :=
    (R.contMDiff_iff_isSmooth_encoding G).mp hsm
  -- Step 2: finite quotient-area Dirichlet energy ⟹ per-copy integrable gradient.
  have hfinflat : ewDirichletEnergyFlat R G ≠ ⊤ := by
    rw [← R.lintegral_quotientGradSq_eq_flat G]; exact henergy
  have hlt : ewDirichletEnergyFlat R G < ⊤ := lt_top_iff_ne_top.mpr hfinflat
  unfold ewDirichletEnergyFlat at hlt
  have hintegr : ∀ n, IntegrableOn
      (Surface.gradSq (encodeDiskFunction (R.diskFunctionPullback G) n)) Surface.disk := by
    intro n
    have hsummand : ∫⁻ w, ENNReal.ofReal
        (Surface.gradSq (encodeDiskFunction (R.diskFunctionPullback G) n) w) ∂volume < ⊤ :=
      (ENNReal.sum_lt_top.mp hlt) n (Finset.mem_univ n)
    have hfi : HasFiniteIntegral
        (Surface.gradSq (encodeDiskFunction (R.diskFunctionPullback G) n)) volume :=
      (hasFiniteIntegral_iff_ofReal
        (Eventually.of_forall fun w =>
          gradSq_nonneg (encodeDiskFunction (R.diskFunctionPullback G) n) w)).mpr hsummand
    have hI : Integrable
        (Surface.gradSq (encodeDiskFunction (R.diskFunctionPullback G) n)) volume :=
      ⟨(measurable_gradSq _).aestronglyMeasurable, hfi⟩
    exact hI.integrableOn
  -- Step 3: membership in the gradient-energy carrier.
  have hmem : encodeDiskFunction (R.diskFunctionPullback G) ∈ GradEnergySmooth k m :=
    ⟨hsmooth, hintegr, encodeDiskFunction_punctureZero _, encodeDiskFunction_seamVal _⟩
  -- Step 4: the encoding solves the model Jacobi equation on all open copies.
  have hjacfield : Surface.IsJacobiField k m (encodeDiskFunction (R.diskFunctionPullback G)) := by
    refine (R.encoding_isJacobiField_iff_openCopies G hsm).mpr ?_
    intro n w _hw
    simpa using congrFun ((R.isGeometricJacobi_iff G).mp hjac) (R.orderedDiskPoint n w)
  -- Step 5: the capstone grants the bound on the encoding.
  have hbdd : Surface.IsBounded (encodeDiskFunction (R.diskFunctionPullback G)) :=
    KsIndex.GammaProducer.bounded_of_jacobi_gradEnergySmooth hk hmem hjacfield
  -- Step 6: descend the bound to the actual quotient function.
  obtain ⟨C, hC⟩ := hbdd
  refine ⟨C, fun q => ?_⟩
  obtain ⟨⟨n, w⟩, rfl⟩ := R.orderedDiskPoint_surjective q
  have hval : encodeDiskFunction (R.diskFunctionPullback G) n w.val.val =
      G (R.orderedDiskPoint n w) := encodeDiskFunction_on_disk (R.diskFunctionPullback G) n w
  rw [← hval]
  exact hC n w.val.val

/-- **Geometric `jacobi_finiteness` (⇒), on the actual EW quotient.** A bounded
smooth geometric Jacobi field `G` on `Ξ_{k,m}` has finite quotient-area Dirichlet
energy (`k ≥ 2`). This is the Caccioppoli half: the bounded field encodes into
`BoundedJacobi`, `bddJacobi_le_energySmooth` gives finite per-copy disk energy on
the chain carrier, and exterior-vanishing of `gradSq e` re-expresses it as the
finite whole-plane flat energy sum `= ewDirichletEnergyFlat`, i.e. the quotient-area
Dirichlet integral. -/
theorem geometric_jacobi_finiteness_forward (R : PaperHalfPeriodRealization k)
    (G : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (hsm : letI := HeightLift.periodChartedSpace R.hC m
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G)
    (hjac : R.IsGeometricJacobi G)
    (hbdd : ∃ C : ℝ, ∀ q, ‖G q‖ ≤ C) :
    ∫⁻ q, ENNReal.ofReal (R.quotientGradSq G q) ∂(R.quotientArea) ≠ ⊤ := by
  have hk : 2 ≤ k := h.out
  -- Package the hypotheses as a bounded geometric Jacobi field and encode it.
  have hbj : encodeDiskFunction (R.diskFunctionPullback G) ∈ Surface.BoundedJacobi k m :=
    R.boundedGeometricJacobi_encoding_mem ⟨G, hsm, hbdd, hjac⟩
  -- Caccioppoli: a bounded smooth Jacobi field has finite smooth energy on the chain carrier.
  obtain ⟨-, hgrad, -, -, -⟩ := bddJacobi_le_energySmooth hk hbj
  -- Each copy's disk gradient energy extends (exterior-zero) to a finite whole-plane integral.
  have hsummand : ∀ n, ∫⁻ w, ENNReal.ofReal
      (Surface.gradSq (encodeDiskFunction (R.diskFunctionPullback G) n) w) ∂volume < ⊤ := by
    intro n
    have hwhole : Integrable
        (Surface.gradSq (encodeDiskFunction (R.diskFunctionPullback G) n)) volume := by
      refine ((hgrad n).integrable_indicator Metric.isOpen_ball.measurableSet).congr
        ((ae_eq_disk_indicator _ ?_).symm)
      intro w hw
      simp [Surface.gradSq,
        fderiv_eq_zero_of_exterior (encodeDiskFunction (R.diskFunctionPullback G) n)
          (encodeDiskFunction_exterior (R.diskFunctionPullback G) n) hw]
    exact (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun w =>
        gradSq_nonneg (encodeDiskFunction (R.diskFunctionPullback G) n) w)).mp
      hwhole.hasFiniteIntegral
  -- Reassemble as the quotient-area Dirichlet integral.
  rw [R.lintegral_quotientGradSq_eq_flat G]
  unfold ewDirichletEnergyFlat
  exact (ENNReal.sum_lt_top.mpr fun n _ => hsummand n).ne

/-- **Geometric `jacobi_finiteness` (full iff), on the actual EW quotient.** For a
smooth geometric Jacobi field `G` on `Ξ_{k,m}` (`k ≥ 2`): `G` is bounded ⟺ its
quotient-area Dirichlet energy is finite. This is tex `jacobi_finiteness`
(ksindexi.tex:1166), both directions, realized on the actual surface. -/
theorem geometric_jacobi_finiteness (R : PaperHalfPeriodRealization k)
    (G : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (hsm : letI := HeightLift.periodChartedSpace R.hC m
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G)
    (hjac : R.IsGeometricJacobi G) :
    (∃ C : ℝ, ∀ q, ‖G q‖ ≤ C) ↔
      ∫⁻ q, ENNReal.ofReal (R.quotientGradSq G q) ∂(R.quotientArea) ≠ ⊤ :=
  ⟨geometric_jacobi_finiteness_forward R G hsm hjac,
   geometric_jacobi_finiteness_reverse R G hsm hjac⟩

end KsIndex.KarcherData.PaperHalfPeriodRealization
