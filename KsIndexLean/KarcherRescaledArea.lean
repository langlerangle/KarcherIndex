module

public import KsIndexLean.KarcherHomothetyMetric
public import KsIndexLean.KarcherQuotientArea
public import KsIndexLean.KarcherGeometricJacobi

@[expose] public section


/-! Area of the homothetically rescaled EW disk charts and period quotient. -/
noncomputable section
open MeasureTheory
open scoped ENNReal KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData

/-- Disk-coordinate area from the induced metric of the scaled immersion. -/
def scaledEWAreaMeasure (k : ℕ) (c : ℝ) : Measure ℂ :=
  volume.withDensity (fun w => ENNReal.ofReal (c ^ 2 * Surface.rho k w ^ 2))

lemma scaledEWAreaMeasure_eq (k : ℕ) (c : ℝ) :
    scaledEWAreaMeasure k c = ENNReal.ofReal (c ^ 2) • ewAreaMeasure k := by
  unfold scaledEWAreaMeasure ewAreaMeasure
  have he : (fun w : ℂ => ENNReal.ofReal (c ^ 2 * Surface.rho k w ^ 2)) =
      ENNReal.ofReal (c ^ 2) • (fun w : ℂ => ENNReal.ofReal (Surface.rho k w ^ 2)) := by
    funext w
    exact ENNReal.ofReal_mul (sq_nonneg c)
  rw [he, withDensity_smul' _ _ ENNReal.ofReal_ne_top]

def scaledEWDiskMeasure (k : ℕ) (c : ℝ) : Measure (PuncturedClosedDisk k) :=
  (scaledEWAreaMeasure k c).comap (fun w => w.val.val)

lemma scaledEWDiskMeasure_eq (k : ℕ) (c : ℝ) :
    scaledEWDiskMeasure k c = ENNReal.ofReal (c ^ 2) • ewDiskMeasure k := by
  rw [scaledEWDiskMeasure, scaledEWAreaMeasure_eq, Measure.comap_smul]
  rfl

namespace PaperHalfPeriodRealization
open scoped QuotientArea
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

/-- The declared area weight is the area of the actual scaled chart. -/
lemma scaled_centeredChart_area (c : ℝ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    chartAreaDensity (c • R.centeredChart q) (R.chartCenter q) =
      c ^ 2 * Surface.rho k (R.chartCenter q) ^ 2 := by
  have ht : R.chartCenter q ∈ (HeightLift.liftChart R.hC q).target :=
    (HeightLift.liftChart R.hC q).map_source (HeightLift.liftChart_mem R.hC q)
  rw [chartAreaDensity_homothety ((R.centeredChart_contDiffAt q ht).differentiableAt (by simp)),
    R.centeredChart_areaDensity_center]

/-- Assemble all ordered disk area pushforwards after ambient scaling. -/
def scaledQuotientArea (c : ℝ) : Measure
    (HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) :=
  ∑ n : ZMod (2*m), Measure.map (R.orderedDiskPoint n) (scaledEWDiskMeasure k c)

lemma scaledQuotientArea_eq (c : ℝ) :
    R.scaledQuotientArea (m := m) c = ENNReal.ofReal (c ^ 2) • R.quotientArea := by
  simp only [scaledQuotientArea, scaledEWDiskMeasure_eq, quotientArea, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro n _
  exact Measure.map_smul _ (R.measurable_orderedDiskPoint n).aemeasurable

end PaperHalfPeriodRealization
end KsIndex.KarcherData
#print axioms KsIndex.KarcherData.scaledEWAreaMeasure_eq
#print axioms KsIndex.KarcherData.PaperHalfPeriodRealization.scaled_centeredChart_area
#print axioms KsIndex.KarcherData.PaperHalfPeriodRealization.scaledQuotientArea_eq
