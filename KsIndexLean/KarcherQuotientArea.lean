module

public import KsIndexLean.KarcherDiskMeasure
public import KsIndexLean.KarcherDiskCopyTopology
public import KsIndexLean.KarcherTestFunctionTransport

@[expose] public section


/-! Borel measure on the actual EW period quotient obtained by summing its
ordered disk area measures. Local induced-area compatibility is a separate
proof obligation; the integration formula here describes the construction. -/
noncomputable section
open MeasureTheory
open scoped ENNReal Classical
namespace KsIndex.KarcherData
namespace QuotientArea
scoped instance puncturedPlaneBorelSpace (k : ℕ) : BorelSpace (PuncturedPlane k) :=
  inferInstanceAs (BorelSpace {w : ℂ // w ∉ Surface.punctures k})
scoped instance puncturedClosedDiskBorelSpace (k : ℕ) : BorelSpace (PuncturedClosedDisk k) :=
  inferInstanceAs (BorelSpace {w : PuncturedPlane k // ‖w.val‖ ≤ 1})
scoped instance periodQuotientMeasurableSpace {P : Type*} [TopologicalSpace P]
    {F : P → PeriodTarget} (m : ℕ) : MeasurableSpace (HeightLift.PeriodQuotient F m) := borel _
scoped instance periodQuotientBorelSpace {P : Type*} [TopologicalSpace P]
    {F : P → PeriodTarget} (m : ℕ) : BorelSpace (HeightLift.PeriodQuotient F m) := ⟨rfl⟩
end QuotientArea
open scoped QuotientArea
lemma ewDiskMeasure_map_coe {k : ℕ} (hk : 2 ≤ k) :
    Measure.map (fun w : PuncturedClosedDisk k => w.val.val) (ewDiskMeasure k) =
      (ewAreaMeasure k).restrict Surface.disk := by
  rw [ewDiskMeasure, measurableEmbedding_puncturedClosedDisk_coe.map_comap]
  apply Measure.restrict_congr_set
  have hc : ∀ᵐ w : ℂ ∂ewAreaMeasure k, ‖w‖ ≠ 1 :=
    ae_iff.mpr (by simpa only [not_not] using (ewAreaMeasure_unitCircle_null (k := k)))
  filter_upwards [hc] with w hw
  apply propext
  constructor
  · rintro ⟨v, rfl⟩
    apply SurfaceForm.mem_disk_iff.mpr
    exact lt_of_le_of_ne v.property hw
  · intro hd
    have hn := SurfaceForm.mem_disk_iff.mp hd
    have hp : w ∉ Surface.punctures k := by
      intro hp
      exact (ne_of_lt hn) (puncture_norm hk hp)
    exact ⟨⟨⟨w, hp⟩, hn.le⟩, rfl⟩

lemma lintegral_ewDiskMeasure {k : ℕ} (hk : 2 ≤ k) (f : ℂ → ℝ≥0∞) :
    ∫⁻ w : PuncturedClosedDisk k, f w.val.val ∂ewDiskMeasure k =
      ∫⁻ w in Surface.disk, f w ∂ewAreaMeasure k := by
  rw [← measurableEmbedding_puncturedClosedDisk_coe.lintegral_map f,
    ewDiskMeasure_map_coe hk]

namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

lemma measurable_orderedDiskPoint (n : ZMod (2*m)) : Measurable (R.orderedDiskPoint n) :=
  (R.continuous_orderedDiskPoint n).measurable

/-- Sum of the area pushforwards of all ordered half-period copies. The
boundary has zero disk area; there is no averaging by the number of copies. -/
def quotientArea : Measure
    (HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) :=
  ∑ n : ZMod (2*m), Measure.map (R.orderedDiskPoint n) (ewDiskMeasure k)

lemma lintegral_quotientArea
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ q, f q ∂(R.quotientArea) = ∑ n : ZMod (2*m),
      ∫⁻ w, f (R.orderedDiskPoint n w) ∂ewDiskMeasure k := by
  rw [quotientArea, lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro n _
  exact lintegral_map hf (R.measurable_orderedDiskPoint n)

/-- Disk-coordinate pullback, extended by zero where the coordinate does not
represent a point of the closed punctured disk. -/
def areaPullback
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℝ≥0∞)
    (n : ZMod (2*m)) (w : ℂ) : ℝ≥0∞ :=
  if hw : w ∉ Surface.punctures k ∧ ‖w‖ ≤ 1 then
    f (R.orderedDiskPoint n ⟨⟨w, hw.1⟩, hw.2⟩) else 0

lemma lintegral_quotientArea_disk
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ q, f q ∂(R.quotientArea) = ∑ n : ZMod (2*m),
      ∫⁻ w in Surface.disk, R.areaPullback f n w ∂ewAreaMeasure k := by
  rw [R.lintegral_quotientArea f hf]
  apply Finset.sum_congr rfl
  intro n _
  rw [← lintegral_ewDiskMeasure h.out (R.areaPullback f n)]
  apply lintegral_congr
  intro w
  simp only [areaPullback, dite_eq_left (show w.val.val ∉ Surface.punctures k ∧ ‖w.val.val‖ ≤ 1
    from ⟨w.val.property, w.property⟩)]
  rfl

end PaperHalfPeriodRealization
end KsIndex.KarcherData
