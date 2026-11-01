module

public import KsIndexLean.KarcherSeamAreaCoverage
public import KsIndexLean.KarcherPolarizedForm

@[expose] public section


/-! Signed and vector-valued integration on the actual EW period quotient.
These formulas preserve every ordered copy, with no normalization factor. -/
noncomputable section
open MeasureTheory Set
namespace KsIndex.KarcherData
open scoped QuotientArea

lemma integral_ewDiskMeasure {k : ℕ} (hk : 2 ≤ k)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℂ → E) :
    ∫ w : PuncturedClosedDisk k, f w.val.val ∂ewDiskMeasure k =
      ∫ w in Surface.disk, f w ∂ewAreaMeasure k := by
  rw [← measurableEmbedding_puncturedClosedDisk_coe.integral_map,
    ewDiskMeasure_map_coe hk]

lemma integrable_ewDiskMeasure_iff {k : ℕ} (hk : 2 ≤ k)
    {E : Type*} [NormedAddCommGroup E] (f : ℂ → E) :
    Integrable (fun w : PuncturedClosedDisk k => f w.val.val) (ewDiskMeasure k) ↔
      IntegrableOn f Surface.disk (ewAreaMeasure k) := by
  have he := measurableEmbedding_puncturedClosedDisk_coe.integrable_map_iff
    (μ := ewDiskMeasure k) (g := f)
  rw [ewDiskMeasure_map_coe hk] at he
  exact he.symm

namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma integrable_quotientArea_iff
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → E)
    (hf : StronglyMeasurable f) :
    Integrable f R.quotientArea ↔ ∀ n : ZMod (2*m),
      Integrable (f ∘ R.orderedDiskPoint n) (ewDiskMeasure k) := by
  simp only [quotientArea, integrable_finsetSum_measure, Finset.mem_univ, forall_const]
  exact forall_congr' (fun n => integrable_map_measure hf.aestronglyMeasurable
    (R.measurable_orderedDiskPoint n).aemeasurable)

omit [CompleteSpace E] in
lemma integral_quotientArea
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → E)
    (hf : StronglyMeasurable f)
    (hi : ∀ n : ZMod (2*m), Integrable (f ∘ R.orderedDiskPoint n) (ewDiskMeasure k)) :
    ∫ q, f q ∂(R.quotientArea) = ∑ n : ZMod (2*m),
      ∫ w, f (R.orderedDiskPoint n w) ∂ewDiskMeasure k := by
  have hm : ∀ n : ZMod (2*m), Integrable f (Measure.map (R.orderedDiskPoint n) (ewDiskMeasure k)) :=
    fun n => (integrable_map_measure hf.aestronglyMeasurable
      (R.measurable_orderedDiskPoint n).aemeasurable).mpr (hi n)
  rw [quotientArea, integral_finsetSum_measure (fun n _ => hm n)]
  apply Finset.sum_congr rfl
  intro n _
  exact integral_map (R.measurable_orderedDiskPoint n).aemeasurable hf.aestronglyMeasurable

/-- Integrability on the quotient is precisely weighted integrability on all
ordered disks, for the existing paper encoding. -/
lemma integrable_quotientArea_iff_encoding
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (hf : StronglyMeasurable f) :
    Integrable f R.quotientArea ↔ ∀ n : ZMod (2*m),
      IntegrableOn (encodeDiskFunction (R.diskFunctionPullback f) n)
        Surface.disk (ewAreaMeasure k) := by
  rw [R.integrable_quotientArea_iff f hf]
  apply forall_congr'
  intro n
  rw [← integrable_ewDiskMeasure_iff h.out]
  have he : (f ∘ R.orderedDiskPoint n) =
      (fun w : PuncturedClosedDisk k => encodeDiskFunction (R.diskFunctionPullback f) n w.val.val) := by
    funext w
    exact (encodeDiskFunction_on_disk (R.diskFunctionPullback f) n w).symm
  rw [he]

/-- Signed complex integration agrees with the weighted paper encoding. -/
lemma integral_quotientArea_encoding
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (hf : StronglyMeasurable f) (hi : Integrable f R.quotientArea) :
    ∫ q, f q ∂(R.quotientArea) = ∑ n : ZMod (2*m),
      ∫ z in Surface.disk, encodeDiskFunction (R.diskFunctionPullback f) n z ∂ewAreaMeasure k := by
  rw [R.integral_quotientArea f hf ((R.integrable_quotientArea_iff f hf).mp hi)]
  apply Finset.sum_congr rfl
  intro n _
  rw [← integral_ewDiskMeasure h.out]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w =>
    (encodeDiskFunction_on_disk (R.diskFunctionPullback f) n w).symm)

end PaperHalfPeriodRealization
end KsIndex.KarcherData
