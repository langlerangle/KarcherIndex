module

public import KsIndexLean.KarcherChartPairing

@[expose] public section


/-! Actual mixed gradient densities in both disk-copy parametrizations. -/
noncomputable section
open Set Topology
open scoped Topology KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)
  (G H : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)

lemma evenCopy_inverseMetricPairing (j : ℤ) (w : PuncturedClosedDisk k) (hw : ‖w.val.val‖ < 1) :
    chartInvMetricGradInner (R.centeredChart (R.evenDiskPoint j w))
      (G ∘ (HeightLift.periodChart R.hC m (R.evenPeriodPoint m j w)).symm)
      (H ∘ (HeightLift.periodChart R.hC m (R.evenPeriodPoint m j w)).symm) w.val.val =
      ((Surface.rho k w.val.val ^ 2)⁻¹ : ℝ) •
        GradOrtho.gradInner (encodeDiskFunction (R.diskFunctionPullback G) (evenCopyIndex (j : ZMod m)))
          (encodeDiskFunction (R.diskFunctionPullback H) (evenCopyIndex (j : ZMod m))) w.val.val := by
  have hm : ∀ d, euclideanSq (fderiv ℝ (R.centeredChart (R.evenDiskPoint j w)) w.val.val d) =
      Surface.rho k w.val.val ^ 2 * ‖d‖ ^ 2 := by
    intro d
    rw [(R.centeredChart_finite_differential _ w.val (R.evenDiskPoint_projection j w)).fderiv]
    exact ewRealDifferential_metric h.out w.val.val d
  rw [chartInvMetricGradInner_of_conformal (rho_sq_pos h.out w.val.property).ne' hm]
  have hg := (R.upperSeam_glue_germ G j (R.evenDiskPoint j w) w.val
    (R.evenDiskPoint_mem_upper_interior j w hw) (R.evenDiskPoint_projection j w)).trans
      (glue_interior_germ _ _ hw)
  have hh := (R.upperSeam_glue_germ H j (R.evenDiskPoint j w) w.val
    (R.evenDiskPoint_mem_upper_interior j w hw) (R.evenDiskPoint_projection j w)).trans
      (glue_interior_germ _ _ hw)
  change (G ∘ (HeightLift.periodChart R.hC m (R.evenPeriodPoint m j w)).symm) =ᶠ[𝓝 w.val.val]
    encodeDiskFunction (R.diskFunctionPullback G) (evenCopyIndex (j : ZMod m)) at hg
  change (H ∘ (HeightLift.periodChart R.hC m (R.evenPeriodPoint m j w)).symm) =ᶠ[𝓝 w.val.val]
    encodeDiskFunction (R.diskFunctionPullback H) (evenCopyIndex (j : ZMod m)) at hh
  simp only [GradOrtho.gradInner, hg.fderiv_eq, hh.fderiv_eq]

lemma oddCopy_inverseMetricPairing (j : ℤ) (w : PuncturedClosedDisk k)
    (hw : ‖w.val.val‖ < 1) (hw0 : w.val.val ≠ 0) :
    chartInvMetricGradInner
      (centeredLiftAmbient R.C R.t ∘ R.lowerParameterLift (R.oddDiskPoint j w) w.val)
      (fun z => G (HeightLift.periodQuotientMap m (R.lowerParameterLift (R.oddDiskPoint j w) w.val z)))
      (fun z => H (HeightLift.periodQuotientMap m (R.lowerParameterLift (R.oddDiskPoint j w) w.val z)))
      w.val.val = ((Surface.rho k w.val.val ^ 2)⁻¹ : ℝ) •
        GradOrtho.gradInner (encodeDiskFunction (R.diskFunctionPullback G) (oddCopyIndex (j : ZMod m)))
          (encodeDiskFunction (R.diskFunctionPullback H) (oddCopyIndex (j : ZMod m))) w.val.val := by
  let v : PuncturedPlane k := ⟨((starRingEnd ℂ) w.val.val)⁻¹,
    inverse_conjugate_not_puncture w.val.property⟩
  have hv : v.val = Bracket.σ w.val.val := by simp [v, Bracket.σ]
  have hp : HeightLift.projection (R.oddDiskPoint j w) = finiteParameter v := by
    rw [R.oddDiskPoint_projection]
    exact parameterSeamReflection_finite h.out w.val hw0 (inverse_conjugate_not_puncture w.val.property)
  rw [chartInvMetricGradInner_of_conformal (rho_sq_pos h.out w.val.property).ne'
    (R.lowerParameterLift_metric _ w.val v hw0 hv hp)]
  have hs : parameterSeamReflection h.out (HeightLift.projection (R.oddDiskPoint j w)) =
      finiteParameter w.val := by rw [R.oddDiskPoint_projection, parameterSeamReflection_involutive]
  have hg := (R.lowerSeam_glue_germ G j (R.oddDiskPoint j w) w.val
    (R.oddDiskPoint_mem_lower_interior j w hw) hs).trans (glue_interior_germ _ _ hw)
  have hh := (R.lowerSeam_glue_germ H j (R.oddDiskPoint j w) w.val
    (R.oddDiskPoint_mem_lower_interior j w hw) hs).trans (glue_interior_germ _ _ hw)
  simp only [GradOrtho.gradInner, hg.fderiv_eq, hh.fderiv_eq]

end KsIndex.KarcherData.PaperHalfPeriodRealization
