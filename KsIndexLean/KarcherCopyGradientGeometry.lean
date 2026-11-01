module

public import KsIndexLean.KarcherInducedAreaCoverage

@[expose] public section


/-! The disk gradient density is the inverse-metric density of the actual
immersion on even-copy interiors and nonzero odd-copy interiors, using the
actual scalar-function chart germ. -/
noncomputable section
open Set Topology
open scoped Topology KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData

lemma conformal_metric_comp_sigma {k : ℕ} (hk : 2 ≤ k) {X : ℂ → AmbientTriple}
    {z : ℂ} (hz : z ≠ 0) (hp : z ∉ Surface.punctures k)
    (hd : DifferentiableAt ℝ X (Bracket.σ z))
    (hm : ∀ d : ℂ, euclideanSq (fderiv ℝ X (Bracket.σ z) d) =
      Surface.rho k (Bracket.σ z) ^ 2 * ‖d‖ ^ 2) (d : ℂ) :
    euclideanSq (fderiv ℝ (X ∘ Bracket.σ) z d) = Surface.rho k z ^ 2 * ‖d‖ ^ 2 := by
  rw [fderiv_comp z hd (SigmaDeriv.hasFDerivAt_sigmaR hz).differentiableAt,
    ContinuousLinearMap.comp_apply, hm, rho_sigma hk hz hp]
  change (‖z‖ ^ 2 * Surface.rho k z) ^ 2 *
    ‖fderiv ℝ (fun w : ℂ => 1 / (starRingEnd ℂ) w) z d‖ ^ 2 = _
  rw [SigmaDeriv.fderiv_sigmaR_apply hz]
  simp only [norm_mul, norm_neg, norm_inv, norm_pow, Complex.norm_conj]
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  field_simp

namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

lemma lowerParameterLift_metric
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w v : PuncturedPlane k) (hw : w.val ≠ 0) (hv : v.val = Bracket.σ w.val)
    (hp : HeightLift.projection q = finiteParameter v) (d : ℂ) :
    euclideanSq (fderiv ℝ (centeredLiftAmbient R.C R.t ∘ R.lowerParameterLift q w) w.val d) =
      Surface.rho k w.val ^ 2 * ‖d‖ ^ 2 := by
  have hg : (centeredLiftAmbient R.C R.t ∘ R.lowerParameterLift q w) =ᶠ[𝓝 w.val]
      (R.centeredChart q ∘ Bracket.σ) := by
    filter_upwards [R.lowerParameterLift_finite_germ q w v hw hv hp] with z hz
    exact congrArg (centeredLiftAmbient R.C R.t) hz
  rw [hg.fderiv_eq]
  have ht : Bracket.σ w.val ∈ (HeightLift.liftChart R.hC q).target := by
    rw [← hv, ← R.chartCenter_finite q v hp]
    exact (HeightLift.liftChart R.hC q).map_source (HeightLift.liftChart_mem R.hC q)
  apply conformal_metric_comp_sigma h.out hw w.property
    ((R.centeredChart_contDiffAt q ht).differentiableAt (by simp))
  intro a
  rw [← hv, (R.centeredChart_finite_differential q v hp).fderiv]
  exact ewRealDifferential_metric h.out v.val a

lemma evenCopy_inverseMetricGradient
    (G : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (j : ℤ) (w : PuncturedClosedDisk k) (hw : ‖w.val.val‖ < 1) :
    chartInvMetricGradSq (R.centeredChart (R.evenDiskPoint j w))
      (G ∘ (HeightLift.periodChart R.hC m (R.evenPeriodPoint m j w)).symm) w.val.val =
    (Surface.rho k w.val.val ^ 2)⁻¹ *
      Surface.gradSq (encodeDiskFunction (R.diskFunctionPullback G) (evenCopyIndex (j : ZMod m)))
        w.val.val := by
  rw [chartInvMetricGradSq_ew h.out w.val.property
    (R.centeredChart_finite_differential _ w.val (R.evenDiskPoint_projection j w))]
  have hg := (R.upperSeam_glue_germ G j (R.evenDiskPoint j w) w.val
    (R.evenDiskPoint_mem_upper_interior j w hw) (R.evenDiskPoint_projection j w)).trans
      (glue_interior_germ _ _ hw)
  change (G ∘ (HeightLift.periodChart R.hC m (R.evenPeriodPoint m j w)).symm) =ᶠ[𝓝 w.val.val]
    encodeDiskFunction (R.diskFunctionPullback G) (evenCopyIndex (j : ZMod m)) at hg
  simp only [Surface.gradSq, hg.fderiv_eq]

lemma oddCopy_inverseMetricGradient
    (G : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (j : ℤ) (w : PuncturedClosedDisk k) (hw : ‖w.val.val‖ < 1) (hw0 : w.val.val ≠ 0) :
    chartInvMetricGradSq
      (centeredLiftAmbient R.C R.t ∘ R.lowerParameterLift (R.oddDiskPoint j w) w.val)
      (fun z => G (HeightLift.periodQuotientMap m (R.lowerParameterLift (R.oddDiskPoint j w) w.val z)))
      w.val.val = (Surface.rho k w.val.val ^ 2)⁻¹ *
      Surface.gradSq (encodeDiskFunction (R.diskFunctionPullback G) (oddCopyIndex (j : ZMod m)))
        w.val.val := by
  let v : PuncturedPlane k := ⟨((starRingEnd ℂ) w.val.val)⁻¹,
    inverse_conjugate_not_puncture w.val.property⟩
  have hv : v.val = Bracket.σ w.val.val := by simp [v, Bracket.σ]
  have hp : HeightLift.projection (R.oddDiskPoint j w) = finiteParameter v := by
    rw [R.oddDiskPoint_projection]
    exact parameterSeamReflection_finite h.out w.val hw0
      (inverse_conjugate_not_puncture w.val.property)
  rw [chartInvMetricGradSq_of_conformal (rho_sq_pos h.out w.val.property).ne'
    (R.lowerParameterLift_metric _ w.val v hw0 hv hp)]
  have hs : parameterSeamReflection h.out (HeightLift.projection (R.oddDiskPoint j w)) =
      finiteParameter w.val := by rw [R.oddDiskPoint_projection, parameterSeamReflection_involutive]
  have hg := (R.lowerSeam_glue_germ G j (R.oddDiskPoint j w) w.val
    (R.oddDiskPoint_mem_lower_interior j w hw) hs).trans (glue_interior_germ _ _ hw)
  simp only [Surface.gradSq, hg.fderiv_eq]

end PaperHalfPeriodRealization
end KsIndex.KarcherData
