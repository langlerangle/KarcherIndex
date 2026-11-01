module

public import KsIndexLean.KarcherQuotientIntegral
public import KsIndexLean.KarcherCopyGradientGeometry

@[expose] public section


/-! Assembly of scalar densities on the disjoint open copies of the actual
quotient. Values on the proved area-null seam set are set to zero. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.KarcherData
open scoped QuotientArea
namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)
variable {E : Type*} [AddCommMonoid E]

/-- Assemble densities on the open copies, with zero on their null boundary. -/
def assembleCopyDensity (d : ZMod (2*m) → ℂ → E)
    (q : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) : E :=
  ∑ n : ZMod (2*m), (R.quotientCopyInterior n).indicator
    (fun x => d n (R.diskCoordinate x).val.val) q

lemma assembleCopyDensity_ordered (d : ZMod (2*m) → ℂ → E)
    (n : ZMod (2*m)) (w : PuncturedClosedDisk k) (hw : ‖w.val.val‖ < 1) :
    R.assembleCopyDensity d (R.orderedDiskPoint n w) = d n w.val.val := by
  classical
  simp [assembleCopyDensity, Set.indicator, R.orderedDiskPoint_mem_copyInterior, hw,
    R.diskCoordinate_orderedDiskPoint]

lemma assembleCopyDensity_seam (d : ZMod (2*m) → ℂ → E)
    {q : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m}
    (hq : q ∈ R.quotientSeams) : R.assembleCopyDensity d q = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro n _
  apply Set.indicator_of_notMem
  intro hn
  obtain ⟨w, hw, rfl⟩ := hn
  exact (ne_of_lt hw) ((R.orderedDiskPoint_mem_quotientSeams n w).mp hq)

lemma measurable_assembleCopyDensity
    [MeasurableSpace E] [MeasurableAdd₂ E]
    (d : ZMod (2*m) → ℂ → E) (hd : ∀ n, Measurable (d n)) :
    Measurable (R.assembleCopyDensity d) := by
  classical
  apply Finset.measurable_sum
  intro n _
  exact ((hd n).comp R.continuous_diskCoordinate_val.measurable).indicator
    (R.isOpen_quotientCopyInterior n).measurableSet

lemma ae_ewDiskMeasure_interior :
    ∀ᵐ w : PuncturedClosedDisk k ∂ewDiskMeasure k, ‖w.val.val‖ < 1 := by
  have hn : ∀ᵐ w : PuncturedClosedDisk k ∂ewDiskMeasure k, ‖w.val.val‖ ≠ 1 :=
    ae_iff.mpr (by simpa only [not_not] using ewDiskMeasure_boundary_null h.out)
  filter_upwards [hn] with w hw
  exact lt_of_le_of_ne w.property hw

lemma lintegral_assembleCopyDensity (d : ZMod (2*m) → ℂ → ℝ)
    (hd : ∀ n, Measurable (d n)) :
    ∫⁻ q, ENNReal.ofReal (R.assembleCopyDensity d q) ∂(R.quotientArea) =
      ∑ n : ZMod (2*m), ∫⁻ z in Surface.disk, ENNReal.ofReal (d n z) ∂ewAreaMeasure k := by
  rw [R.lintegral_quotientArea _ (R.measurable_assembleCopyDensity d hd).ennreal_ofReal]
  apply Finset.sum_congr rfl
  intro n _
  rw [← lintegral_ewDiskMeasure h.out]
  apply lintegral_congr_ae
  filter_upwards [ae_ewDiskMeasure_interior (k := k)] with w hw
  rw [R.assembleCopyDensity_ordered d n w hw]

lemma ae_diskCoordinate_ne_zero :
    ∀ᵐ x ∂(R.quotientArea (m := m)), (R.diskCoordinate x).val.val ≠ 0 := by
  rw [quotientArea, ae_finsetSum_measure_iff]
  intro n _
  apply (ae_map_iff (p := fun x => (R.diskCoordinate x).val.val ≠ 0)
    (R.measurable_orderedDiskPoint n).aemeasurable
    ((isClosed_eq R.continuous_diskCoordinate_val
      (continuous_const (y := (0 : ℂ)))).measurableSet.compl)).mpr
  have hn : ∀ᵐ w : PuncturedClosedDisk k ∂ewDiskMeasure k, w.val.val ≠ 0 := by
    apply ae_of_ae_map (μ := ewDiskMeasure k) (p := fun z : ℂ => z ≠ 0)
      measurableEmbedding_puncturedClosedDisk_coe.measurable.aemeasurable
    rw [ewDiskMeasure_map_coe h.out]
    exact ae_restrict_of_ae ((ewAreaMeasure_ae_regular_coordinate k).mono (fun _ hz => hz.1))
  filter_upwards [hn] with w hw
  simpa only [R.diskCoordinate_orderedDiskPoint] using hw

lemma ae_quotient_interior_nonzero :
    ∀ᵐ x ∂(R.quotientArea (m := m)), ∃ (n : ZMod (2*m)) (w : PuncturedClosedDisk k),
      ‖w.val.val‖ < 1 ∧ w.val.val ≠ 0 ∧ R.orderedDiskPoint n w = x := by
  have hs : ∀ᵐ x ∂(R.quotientArea (m := m)), x ∉ R.quotientSeams :=
    ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using R.quotientArea_seams_null (m := m))
  filter_upwards [hs, R.ae_diskCoordinate_ne_zero (m := m)] with x hx hz
  obtain ⟨⟨n,w⟩, he⟩ := R.orderedDiskPoint_surjective x
  have hnorm : ‖w.val.val‖ ≠ 1 := fun hw => hx (he ▸ (R.orderedDiskPoint_mem_quotientSeams n w).mpr hw)
  refine ⟨n, w, lt_of_le_of_ne w.property hnorm, ?_, he⟩
  simpa only [← he, R.diskCoordinate_orderedDiskPoint] using hz

end PaperHalfPeriodRealization
end KsIndex.KarcherData
