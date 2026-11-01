module

public import KsIndexLean.KarcherJacobiSeamEquation

@[expose] public section


/-! Reconstruction of actual bounded geometric solutions from model fields. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

lemma geometricJacobi_circle_of_encoding
    (G : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (hG : letI := HeightLift.periodChartedSpace R.hC m;
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G)
    (hJ : Surface.IsJacobiField k m (encodeDiskFunction (R.diskFunctionPullback G)))
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w : PuncturedPlane k) (hw : ‖w.val‖ = 1)
    (hp : HeightLift.projection q = finiteParameter w) : R.geometricJacobiAt G q = 0 := by
  let f := G ∘ (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).symm
  have hc := R.chartCenter_finite q w hp
  have hf : ContDiffAt ℝ ∞ f w.val := by
    have hh := R.smooth_quotient_chart_pullback G hG q
    rwa [hc] at hh
  rw [R.geometricJacobiAt_eq_diskJacobi, hc]
  change diskJacobi k f w.val = 0
  obtain ⟨j, hu | hl⟩ := R.seamBands_cover q
  · have hg := R.upperSeam_glue_germ G j q w hu hp
    rw [diskJacobi_congr hg]
    exact diskJacobi_glue_boundary h.out hJ _ hw w.property
      (hf.congr_of_eventuallyEq hg.symm)
  · have hw0 : w.val ≠ 0 := by intro he; simp [he] at hw
    have hfix : Bracket.σ w.val = w.val := Bracket.σ_self hw
    have hs : parameterSeamReflection h.out (HeightLift.projection q) = finiteParameter w := by
      rw [hp, parameterSeamReflection_finite h.out w hw0
        (inverse_conjugate_not_puncture w.property)]
      congr 1
      apply Subtype.ext
      simpa only [Bracket.σ, one_div] using hfix
    have hg0 := R.centeredChart_scalar_pullback_germ G q
    rw [hc] at hg0
    have ht : Filter.Tendsto Bracket.σ (𝓝 w.val) (𝓝 w.val) := by
      simpa only [hfix] using (Bracket.continuousAt_σ hw0).tendsto
    have hg := hg0.comp_tendsto ht
    have hlf := R.lowerParameterLift_finite_germ q w w hw0 hfix.symm hp
    have he := R.lowerSeam_glue_germ G j q w hl hs
    have hfg : f ∘ Bracket.σ =ᶠ[𝓝 w.val]
        Surface.glue (encodeDiskFunction (R.diskFunctionPullback G)) (oddCopyIndex (j : ZMod m)) := by
      filter_upwards [hg, hlf, he] with z hz hzl hze
      change f (Bracket.σ z) = _
      change G (HeightLift.periodQuotientMap m ((HeightLift.liftChart R.hC q).symm (Bracket.σ z))) =
        f (Bracket.σ z) at hz
      simp only [Function.comp_apply] at hzl
      rw [← hz, ← hzl]
      exact hze
    have hsf : ContDiffAt ℝ ∞ (f ∘ Bracket.σ) w.val := by
      have hsigma : ContDiffAt ℝ ∞ Bracket.σ w.val := by
        have hconj : ContDiffAt ℝ ∞ (fun z : ℂ => (starRingEnd ℂ) z) w.val :=
          Complex.conjCLE.contDiff.contDiffAt
        change ContDiffAt ℝ ∞ (fun z : ℂ => 1 / (starRingEnd ℂ) z) w.val
        simp only [one_div]
        exact hconj.inv (by simpa using hw0)
      exact (hfix ▸ hf).comp w.val hsigma
    have hh := diskJacobi_comp_sigma h.out hw0 w.property
      (show ContDiffAt ℝ 2 f (Bracket.σ w.val) by simpa only [hfix] using hf.of_le Surface.two_le_infty)
    rw [hfix] at hh
    rw [← hh, diskJacobi_congr hfg]
    exact diskJacobi_glue_boundary h.out hJ _ hw w.property
      (hsf.congr_of_eventuallyEq hfg.symm)

lemma isGeometricJacobi_of_encoding
    (G : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (hG : letI := HeightLift.periodChartedSpace R.hC m;
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G)
    (hJ : Surface.IsJacobiField k m (encodeDiskFunction (R.diskFunctionPullback G))) :
    R.IsGeometricJacobi G := by
  apply (R.isGeometricJacobi_iff G).mpr
  funext x
  by_cases hx : x ∈ R.quotientSeams
  · obtain ⟨q, w, rfl, hw, hp⟩ := R.quotientSeam_circle_lift x hx
    exact R.geometricJacobi_circle_of_encoding G hG hJ q w hw hp
  · obtain ⟨⟨n,w⟩, rfl⟩ := R.orderedDiskPoint_surjective x
    have hw : ‖w.val.val‖ < 1 := lt_of_le_of_ne w.property
      (fun he => hx ((R.orderedDiskPoint_mem_quotientSeams n w).mpr he))
    exact (R.encoding_isJacobiField_iff_openCopies G hG).mp hJ n w hw

lemma encode_boundedJacobiFunction (u : Surface.BoundedJacobi k m) :
    encodeDiskFunction (R.diskFunctionPullback (R.boundedJacobiFunction u)) = u.val := by
  have he : R.diskFunctionPullback (R.boundedJacobiFunction u) =
      restrictSeamFamily u.val u.property.2.2.2.2 :=
    R.diskFunctionEquiv.right_inv _
  rw [he]
  exact encode_restrictSeamFamily u.val _ u.property.2.2.2.1 u.property.1.2.2

/-- Every model field gives a bounded smooth solution of the actual geometric
Jacobi equation, including at seams and infinity. -/
lemma boundedJacobiFunction_isBoundedGeometricJacobi (u : Surface.BoundedJacobi k m) :
    R.IsBoundedGeometricJacobi (R.boundedJacobiFunction u) := by
  have hs : letI := HeightLift.periodChartedSpace R.hC m;
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (R.boundedJacobiFunction u) := by
    apply (R.contMDiff_iff_isSmooth_encoding _).mpr
    rw [R.encode_boundedJacobiFunction]
    exact u.property.1
  refine ⟨hs, R.boundedJacobiFunction_bounded u, R.isGeometricJacobi_of_encoding _ hs ?_⟩
  rw [R.encode_boundedJacobiFunction]
  exact u.property.2.2.1

end KsIndex.KarcherData.PaperHalfPeriodRealization
