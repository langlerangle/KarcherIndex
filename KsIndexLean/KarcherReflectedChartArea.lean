module

public import KsIndexLean.KarcherUpperSeamArea
public import KsIndexLean.KarcherActualChartOverlap

@[expose] public section


/-! The induced area of an actual finite immersion chart after the circle
inversion used as a lower-seam coordinate. -/
noncomputable section
open Set Topology
open scoped Topology KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData

lemma chartAreaDensity_comp_sigma {k : ℕ} (hk : 2 ≤ k) {X : ℂ → AmbientTriple}
    {z : ℂ} (hz : z ≠ 0) (hp : z ∉ Surface.punctures k)
    (hd : DifferentiableAt ℝ X (Bracket.σ z))
    (hm : ∀ d : ℂ, euclideanSq (fderiv ℝ X (Bracket.σ z) d) =
      Surface.rho k (Bracket.σ z) ^ 2 * ‖d‖ ^ 2) :
    chartAreaDensity (X ∘ Bracket.σ) z = Surface.rho k z ^ 2 := by
  apply chartAreaDensity_of_conformal (by positivity)
  intro d
  rw [fderiv_comp z hd (SigmaDeriv.hasFDerivAt_sigmaR hz).differentiableAt,
    ContinuousLinearMap.comp_apply, hm, rho_sigma hk hz hp]
  change (‖z‖ ^ 2 * Surface.rho k z) ^ 2 *
    ‖fderiv ℝ (fun w : ℂ => 1 / (starRingEnd ℂ) w) z d‖ ^ 2 = _
  rw [SigmaDeriv.fderiv_sigmaR_apply hz]
  simp only [norm_mul, norm_neg, norm_inv, norm_pow, Complex.norm_conj]
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  field_simp

namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)] (R : PaperHalfPeriodRealization k)

lemma centeredChart_reflected_areaDensity_field
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w v : PuncturedPlane k) (hw : w.val ≠ 0) (hv : v.val = Bracket.σ w.val)
    (hp : HeightLift.projection q = finiteParameter v) :
    (fun z => chartAreaDensity (R.centeredChart q ∘ Bracket.σ) z) =ᶠ[𝓝 w.val]
      (fun z => Surface.rho k z ^ 2) := by
  have ht : Bracket.σ w.val ∈ (HeightLift.liftChart R.hC q).target := by
    rw [← hv, ← R.chartCenter_finite q v hp]
    exact (HeightLift.liftChart R.hC q).map_source (HeightLift.liftChart_mem R.hC q)
  have hs := (Bracket.continuousAt_σ hw).tendsto
  have hm := R.centeredChart_finite_metric_field q v hp
  rw [hv] at hm
  have htar : ∀ᶠ z in 𝓝 (Bracket.σ w.val), z ∈ (HeightLift.liftChart R.hC q).target :=
    (HeightLift.liftChart R.hC q).open_target.mem_nhds ht
  have hzero : ∀ᶠ z in 𝓝 w.val, z ≠ 0 := isOpen_ne_fun continuous_id continuous_const |>.mem_nhds hw
  have hclosed : IsClosed (Surface.punctures k) :=
    isClosed_eq (continuous_id.pow (2*k)) continuous_const
  filter_upwards [hs.eventually hm, hs.eventually htar, hzero,
    hclosed.isOpen_compl.mem_nhds w.property] with z hz ht hz0 hzp
  exact chartAreaDensity_comp_sigma h.out hz0 hzp
    ((R.centeredChart_contDiffAt q ht).differentiableAt (by simp)) hz

/-- The actual reflected local lift agrees with the ordinary lifted chart
composed with circle inversion near a nonzero finite coordinate. -/
lemma lowerParameterLift_finite_germ
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w v : PuncturedPlane k) (hw : w.val ≠ 0) (hv : v.val = Bracket.σ w.val)
    (hp : HeightLift.projection q = finiteParameter v) :
    R.lowerParameterLift q w =ᶠ[𝓝 w.val]
      ((HeightLift.liftChart R.hC q).symm ∘ Bracket.σ) := by
  have hs := (Bracket.continuousAt_σ hw).tendsto
  have hgv := finite_parameter_chart_germ v
  rw [hv] at hgv
  have hzero : ∀ᶠ z in 𝓝 w.val, z ≠ 0 :=
    isOpen_ne_fun continuous_id continuous_const |>.mem_nhds hw
  filter_upwards [finite_parameter_chart_germ w, hs.eventually hgv, hzero] with z hz hvz hz0
  obtain ⟨hzp, hz⟩ := hz
  obtain ⟨hvp, hvz⟩ := hvz
  change (HeightLift.projection_isLocalHomeomorph R.hC).localInverseAt q
      (parameterSeamReflection h.out ((chartAt ℂ (finiteParameter w)).symm z)) =
    (HeightLift.projection_isLocalHomeomorph R.hC).localInverseAt q
      ((chartAt ℂ (HeightLift.projection q)).symm (Bracket.σ z))
  congr 1
  rw [hz, hp, hvz]
  simpa only [Bracket.σ, one_div] using
    parameterSeamReflection_finite h.out (⟨z,hzp⟩ : PuncturedPlane k) hz0
      (inverse_conjugate_not_puncture hzp)

/-- Area density of the actual ambient immersion composed with the lower
parameter lift, rather than of a separately chosen model parametrization. -/
lemma lowerParameterLift_areaDensity_field
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w v : PuncturedPlane k) (hw : w.val ≠ 0) (hv : v.val = Bracket.σ w.val)
    (hp : HeightLift.projection q = finiteParameter v) :
    (fun z => chartAreaDensity (centeredLiftAmbient R.C R.t ∘ R.lowerParameterLift q w) z)
      =ᶠ[𝓝 w.val] (fun z => Surface.rho k z ^ 2) := by
  have hg : (centeredLiftAmbient R.C R.t ∘ R.lowerParameterLift q w) =ᶠ[𝓝 w.val]
      (R.centeredChart q ∘ Bracket.σ) := by
    filter_upwards [R.lowerParameterLift_finite_germ q w v hw hv hp] with z hz
    exact congrArg (centeredLiftAmbient R.C R.t) hz
  filter_upwards [hg.eventually_nhds, R.centeredChart_reflected_areaDensity_field q w v hw hv hp]
    with z hz hd
  have hzeq : (centeredLiftAmbient R.C R.t ∘ R.lowerParameterLift q w) =ᶠ[𝓝 z]
      (R.centeredChart q ∘ Bracket.σ) := hz
  have he := hzeq.fderiv_eq (𝕜 := ℝ)
  simpa only [chartAreaDensity, chartGramDet, firstFundamentalForm, he] using hd

/-- Continuity of the actual reflected lift on a neighborhood of its center. -/
lemma lowerParameterLift_continuousAt_field
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w v : PuncturedPlane k) (hw : w.val ≠ 0) (hv : v.val = Bracket.σ w.val)
    (hp : HeightLift.projection q = finiteParameter v) :
    ∀ᶠ z in 𝓝 w.val, ContinuousAt (R.lowerParameterLift q w) z := by
  let e := HeightLift.liftChart R.hC q
  have ht : Bracket.σ w.val ∈ e.target := by
    rw [← hv, ← R.chartCenter_finite q v hp]
    exact e.map_source (HeightLift.liftChart_mem R.hC q)
  have htar : ∀ᶠ z in 𝓝 (Bracket.σ w.val), z ∈ e.target := e.open_target.mem_nhds ht
  have hs := (Bracket.continuousAt_σ hw).tendsto
  have hzero : ∀ᶠ z in 𝓝 w.val, z ≠ 0 :=
    isOpen_ne_fun continuous_id continuous_const |>.mem_nhds hw
  filter_upwards [(R.lowerParameterLift_finite_germ q w v hw hv hp).eventually_nhds,
    hs.eventually htar, hzero] with z hz ht hz0
  have heq : R.lowerParameterLift q w =ᶠ[𝓝 z] (e.symm ∘ Bracket.σ) := hz
  exact ((e.continuousAt_symm ht).comp (Bracket.continuousAt_σ hz0)).congr_of_eventuallyEq heq

end PaperHalfPeriodRealization
end KsIndex.KarcherData
