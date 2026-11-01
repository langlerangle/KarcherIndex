module

public import KsIndexLean.KarcherQuotientDensity

@[expose] public section


/-! Dirichlet integration against the actual quotient area. The density below
is expressed in disk coordinates, with its equality to the actual immersion's
inverse-metric gradient density proved separately on each open copy. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData
open scoped QuotientArea

lemma lintegral_ew_eq_disk_of_exterior (k : ℕ) (f : ℂ → ℝ≥0∞)
    (he : ∀ z, 1 < ‖z‖ → f z = 0) :
    ∫⁻ z, f z ∂ewAreaMeasure k = ∫⁻ z in Surface.disk, f z ∂ewAreaMeasure k := by
  rw [← lintegral_indicator SurfaceForm.measurableSet_disk]
  apply lintegral_congr_ae
  filter_upwards [ewAreaMeasure_ae_regular_coordinate k] with z hz
  by_cases hd : z ∈ Surface.disk
  · exact (Set.indicator_of_mem hd f).symm
  · have hn : 1 ≤ ‖z‖ := le_of_not_gt (fun hh => hd (SurfaceForm.mem_disk_iff.mpr hh))
    rw [Set.indicator_of_notMem hd, he z (lt_of_le_of_ne hn hz.2.symm)]

namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)
  (G : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)

/-- Inverse-metric gradient density, extended by zero across the area-null seam
set. The open-copy geometric identifications use actual immersion derivatives. -/
def quotientGradSq := R.assembleCopyDensity (fun n z => (Surface.rho k z ^ 2)⁻¹ *
  Surface.gradSq (encodeDiskFunction (R.diskFunctionPullback G) n) z)

lemma measurable_quotientGradSq : Measurable (R.quotientGradSq G) := by
  apply R.measurable_assembleCopyDensity
  intro n
  exact ((measurable_rho k).pow_const 2).inv.mul (measurable_gradSq _)

lemma quotientGradSq_even_geometry (j : ZMod m) (w : PuncturedClosedDisk k)
    (hw : ‖w.val.val‖ < 1) :
    R.quotientGradSq G (R.orderedDiskPoint (evenCopyIndex j) w) =
      chartInvMetricGradSq (R.centeredChart (R.evenDiskPoint j.val w))
        (G ∘ (HeightLift.periodChart R.hC m (R.evenPeriodPoint m j.val w)).symm) w.val.val := by
  rw [quotientGradSq, R.assembleCopyDensity_ordered _ _ w hw,
    R.evenCopy_inverseMetricGradient G j.val w hw]
  simp

lemma quotientGradSq_odd_geometry (j : ZMod m) (w : PuncturedClosedDisk k)
    (hw : ‖w.val.val‖ < 1) (hw0 : w.val.val ≠ 0) :
    R.quotientGradSq G (R.orderedDiskPoint (oddCopyIndex j) w) =
      chartInvMetricGradSq
        (centeredLiftAmbient R.C R.t ∘ R.lowerParameterLift (R.oddDiskPoint j.val w) w.val)
        (fun z => G (HeightLift.periodQuotientMap m
          (R.lowerParameterLift (R.oddDiskPoint j.val w) w.val z))) w.val.val := by
  rw [quotientGradSq, R.assembleCopyDensity_ordered _ _ w hw,
    R.oddCopy_inverseMetricGradient G j.val w hw hw0]
  simp

/-- Almost everywhere the assembled density is the inverse-metric gradient
of the actual scalar function in an actual immersion parametrization. -/
lemma quotientGradSq_ae_geometry :
    ∀ᵐ x ∂(R.quotientArea),
      ∃ (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k),
        HeightLift.periodQuotientMap m q = x ∧
        (R.quotientGradSq G x = chartInvMetricGradSq (R.centeredChart q)
          (G ∘ (HeightLift.periodChart R.hC m x).symm) w.val ∨
         R.quotientGradSq G x = chartInvMetricGradSq
          (centeredLiftAmbient R.C R.t ∘ R.lowerParameterLift q w)
          (fun z => G (HeightLift.periodQuotientMap m (R.lowerParameterLift q w z))) w.val) := by
  filter_upwards [R.ae_quotient_interior_nonzero (m := m)] with x hx
  obtain ⟨n, w, hw, hw0, rfl⟩ := hx
  obtain ⟨j, rfl | rfl⟩ := copyIndex_cases n
  · refine ⟨R.evenDiskPoint j.val w, w.val, (R.orderedDiskPoint_even j w).symm, Or.inl ?_⟩
    simpa only [R.orderedDiskPoint_even] using R.quotientGradSq_even_geometry G j w hw
  · exact ⟨R.oddDiskPoint j.val w, w.val, (R.orderedDiskPoint_odd j w).symm,
      Or.inr (R.quotientGradSq_odd_geometry G j w hw hw0)⟩

/-- The global quotient-area integral equals the weighted copywise energy. -/
lemma lintegral_quotientGradSq :
    ∫⁻ q, ENNReal.ofReal (R.quotientGradSq G q) ∂(R.quotientArea) =
      ewDirichletEnergyGeom R G := by
  rw [quotientGradSq, R.lintegral_assembleCopyDensity
    (fun n z => (Surface.rho k z ^ 2)⁻¹ *
      Surface.gradSq (encodeDiskFunction (R.diskFunctionPullback G) n) z)
    (fun n => ((measurable_rho k).pow_const 2).inv.mul
      (measurable_gradSq (encodeDiskFunction (R.diskFunctionPullback G) n)))]
  unfold ewDirichletEnergyGeom
  apply Finset.sum_congr rfl
  intro n _
  symm
  apply lintegral_ew_eq_disk_of_exterior
  intro z hz
  simp [Surface.gradSq, fderiv_eq_zero_of_exterior _ (encodeDiskFunction_exterior _ n) hz]

lemma lintegral_quotientGradSq_eq_flat :
    ∫⁻ q, ENNReal.ofReal (R.quotientGradSq G q) ∂(R.quotientArea) = ewDirichletEnergyFlat R G := by
  rw [R.lintegral_quotientGradSq G, R.ewDirichletEnergyGeom_eq_flat G]

end PaperHalfPeriodRealization
end KsIndex.KarcherData
