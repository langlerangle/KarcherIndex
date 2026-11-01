module

public import KsIndexLean.KarcherQuotientJacobi

@[expose] public section


/-! Integrable complex densities assembled over the actual quotient's open
copies. The seam removal uses proved area nullity. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.KarcherData
open scoped QuotientArea

lemma integral_ew_eq_disk_of_exterior (k : ℕ) (f : ℂ → ℂ)
    (he : ∀ z, 1 < ‖z‖ → f z = 0) :
    ∫ z, f z ∂ewAreaMeasure k = ∫ z in Surface.disk, f z ∂ewAreaMeasure k := by
  rw [← integral_indicator SurfaceForm.measurableSet_disk]
  apply integral_congr_ae
  filter_upwards [ewAreaMeasure_ae_regular_coordinate k] with z hz
  by_cases hd : z ∈ Surface.disk
  · exact (Set.indicator_of_mem hd f).symm
  · have hn : 1 ≤ ‖z‖ := le_of_not_gt (fun hh => hd (SurfaceForm.mem_disk_iff.mpr hh))
    rw [Set.indicator_of_notMem hd, he z (lt_of_le_of_ne hn hz.2.symm)]

namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

lemma integrable_assembleCopyDensity_iff (d : ZMod (2*m) → ℂ → ℂ)
    (hd : ∀ n, Measurable (d n)) :
    Integrable (R.assembleCopyDensity d) R.quotientArea ↔
      ∀ n, IntegrableOn (d n) Surface.disk (ewAreaMeasure k) := by
  rw [R.integrable_quotientArea_iff _ (R.measurable_assembleCopyDensity d hd).stronglyMeasurable]
  apply forall_congr'
  intro n
  have he : (R.assembleCopyDensity d ∘ R.orderedDiskPoint n) =ᵐ[ewDiskMeasure k]
      (fun w : PuncturedClosedDisk k => d n w.val.val) := by
    filter_upwards [ae_ewDiskMeasure_interior (k := k)] with w hw
    exact R.assembleCopyDensity_ordered d n w hw
  exact (integrable_congr he).trans (integrable_ewDiskMeasure_iff h.out (d n))

lemma integral_assembleCopyDensity (d : ZMod (2*m) → ℂ → ℂ)
    (hd : ∀ n, Measurable (d n))
    (hi : ∀ n, IntegrableOn (d n) Surface.disk (ewAreaMeasure k)) :
    ∫ x, R.assembleCopyDensity d x ∂(R.quotientArea) =
      ∑ n : ZMod (2*m), ∫ z in Surface.disk, d n z ∂ewAreaMeasure k := by
  have hI := (R.integrable_assembleCopyDensity_iff d hd).mpr hi
  have hM := (R.measurable_assembleCopyDensity d hd).stronglyMeasurable
  rw [R.integral_quotientArea _ hM ((R.integrable_quotientArea_iff _ hM).mp hI)]
  apply Finset.sum_congr rfl
  intro n _
  rw [← integral_ewDiskMeasure h.out (d n)]
  apply integral_congr_ae
  filter_upwards [ae_ewDiskMeasure_interior (k := k)] with w hw
  exact R.assembleCopyDensity_ordered d n w hw

lemma measurable_encoding
    (G : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (hG : Continuous G) (n : ZMod (2*m)) :
    Measurable (encodeDiskFunction (R.diskFunctionPullback G) n) := by
  classical
  have hs : MeasurableSet {w : ℂ | w ∉ Surface.punctures k ∧ ‖w‖ ≤ 1} :=
    ((isClosed_eq (continuous_id.pow (2*k)) continuous_const).measurableSet.compl).inter
      (measurableSet_le continuous_norm.measurable measurable_const)
  have hf : Measurable (fun ws : {w : ℂ | w ∉ Surface.punctures k ∧ ‖w‖ ≤ 1} =>
      (R.diskFunctionPullback G).val (n, ⟨⟨ws.val, ws.property.1⟩, ws.property.2⟩)) :=
    (hG.comp ((R.continuous_orderedDiskPoint n).comp
      ((continuous_subtype_val.subtype_mk fun ws => ws.property.1).subtype_mk
        fun ws => ws.property.2))).measurable
  exact Measurable.dite hf (measurable_const (a := (0 : ℂ))) hs

end PaperHalfPeriodRealization
end KsIndex.KarcherData
