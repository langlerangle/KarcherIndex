module

public import KsIndexLean.KarcherSeamChartSupport

@[expose] public section


/-! Transport of the restricted EW area measure through local inverses of
unfolded seam coordinates. Only measurability on the coordinate neighborhood
is required; no assertion about the inverse outside that neighborhood is used. -/
noncomputable section
open Set MeasureTheory Topology
open scoped Topology
namespace KsIndex.KarcherData
open scoped QuotientArea

lemma ewAreaMeasure_ae_regular_coordinate (k : ℕ) :
    ∀ᵐ z : ℂ ∂ewAreaMeasure k, z ≠ 0 ∧ ‖z‖ ≠ 1 := by
  have hz : ∀ᵐ z : ℂ ∂ewAreaMeasure k, z ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_eq_eq_singleton, ewAreaMeasure] using
      (withDensity_absolutelyContinuous volume
        (fun z : ℂ => ENNReal.ofReal (Surface.rho k z ^ 2)) (measure_singleton (0 : ℂ)))
  have hc : ∀ᵐ z : ℂ ∂ewAreaMeasure k, ‖z‖ ≠ 1 :=
    ae_iff.mpr (by simpa only [not_not] using (ewAreaMeasure_unitCircle_null (k := k)))
  exact hz.and hc

namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

/-- A local inverse recovering the pair almost everywhere transports EW area
back to precisely the corresponding restriction of quotient area. -/
lemma map_seam_inverse_restrict {n j : ZMod (2*m)} (hnj : n ≠ j)
    {U : Set ℂ} (hU : MeasurableSet U)
    (g : ℂ → HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m)
    (hg : AEMeasurable g ((ewAreaMeasure k).restrict U))
    (hinv : ∀ z ∈ U, ∀ x,
      x ∈ R.quotientCopyInterior n ∪ R.quotientCopyInterior j →
      R.seamPairCoordinate n x = z → z ≠ 0 → ‖z‖ ≠ 1 → g z = x) :
    Measure.map g ((ewAreaMeasure k).restrict U) =
      ((R.quotientArea).restrict (R.quotientCopyInterior n ∪ R.quotientCopyInterior j)).restrict
        (R.seamPairCoordinate n ⁻¹' U) := by
  let ν := (R.quotientArea).restrict (R.quotientCopyInterior n ∪ R.quotientCopyInterior j)
  have hc := R.measurable_seamPairCoordinate n
  have hm : Measure.map (R.seamPairCoordinate n) (ν.restrict (R.seamPairCoordinate n ⁻¹' U)) =
      (ewAreaMeasure k).restrict U := by
    rw [← Measure.restrict_map hc hU]
    exact congrArg (fun μ : Measure ℂ => μ.restrict U) (R.map_seamPairCoordinate_area hnj)
  have hg' : AEMeasurable g
      (Measure.map (R.seamPairCoordinate n) (ν.restrict (R.seamPairCoordinate n ⁻¹' U))) := by
    rw [hm]
    exact hg
  have hreg : ∀ᵐ x ∂ν.restrict (R.seamPairCoordinate n ⁻¹' U),
      R.seamPairCoordinate n x ≠ 0 ∧ ‖R.seamPairCoordinate n x‖ ≠ 1 := by
    apply ae_of_ae_map (μ := ν.restrict (R.seamPairCoordinate n ⁻¹' U))
      (p := fun z : ℂ => z ≠ 0 ∧ ‖z‖ ≠ 1) hc.aemeasurable
    rw [hm]
    exact ae_restrict_of_ae (ewAreaMeasure_ae_regular_coordinate k)
  have hp : ∀ᵐ x ∂ν, x ∈ R.quotientCopyInterior n ∪ R.quotientCopyInterior j :=
    ae_restrict_mem ((R.isOpen_quotientCopyInterior n).union (R.isOpen_quotientCopyInterior j)).measurableSet
  rw [← hm, AEMeasurable.map_map_of_aemeasurable hg' hc.aemeasurable]
  calc
    _ = Measure.map id (ν.restrict (R.seamPairCoordinate n ⁻¹' U)) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_of_ae hp, ae_restrict_mem (hc hU), hreg] with x hx hxu hxr
      exact hinv _ hxu x hx rfl hxr.1 hxr.2
    _ = _ := Measure.map_id

end PaperHalfPeriodRealization
end KsIndex.KarcherData
