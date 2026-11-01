module

public import KsIndexLean.DiskTrace

@[expose] public section


open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma integral_radialField_le {a b : ℝ} (ha : 0 < a) {U : ℂ → ℂ →L[ℝ] ℂ}
    (h1 : MemLp (fun z => U z 1) 2 (volume.restrict (annulusSet a b)))
    (hI : MemLp (fun z => U z Complex.I) 2 (volume.restrict (annulusSet a b))) :
    (∫ z in annulusSet a b, ‖radialField U z‖ ^ 2) ≤
      2 * ∫ z in annulusSet a b, (‖U z 1‖ ^ 2 + ‖U z Complex.I‖ ^ 2) := by
  have hf := memLp_radialField ha h1 hI
  have hi1 := (memLp_two_iff_integrable_sq_norm h1.aestronglyMeasurable).mp h1
  have hiI := (memLp_two_iff_integrable_sq_norm hI.aestronglyMeasurable).mp hI
  rw [← integral_const_mul]
  apply integral_mono_ae (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable |>.mp hf)
    ((hi1.add hiI).const_mul 2)
  filter_upwards [enorm_radialField_sq_le ha U] with z hz
  have hfinite : 2 * (‖U z 1‖ₑ ^ (2 : ℕ) + ‖U z Complex.I‖ₑ ^ (2 : ℕ)) ≠ ∞ := by
    finiteness
  have h := ENNReal.toReal_mono hfinite hz
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness)] at h
  simpa using h

lemma collar_norm_sq_integrable (f : L2C) :
    IntegrableOn (fun z => ‖f z‖ ^ 2) (annulusSet (1 / 2 : ℝ) 1) volume :=
  (memLp_two_iff_integrable_sq_norm (collar_memLp f).aestronglyMeasurable).mp (collar_memLp f)

lemma diskTrace_annular_bound (u : ComplexH1) :
    ‖diskTrace u‖ ^ 2 ≤
      8 * (∫ z in annulusSet (1 / 2 : ℝ) 1, ‖valueCLM u z‖ ^ 2) +
      4 * ∫ z in annulusSet (1 / 2 : ℝ) 1, (‖dxLp u z‖ ^ 2 + ‖dyLp u z‖ ^ 2) := by
  have h1 : MemLp (fun z => Dxy (dxLp u) (dyLp u) z 1) 2
      (volume.restrict (annulusSet (1 / 2 : ℝ) 1)) := by simpa using collar_memLp (dxLp u)
  have hI : MemLp (fun z => Dxy (dxLp u) (dyLp u) z Complex.I) 2
      (volume.restrict (annulusSet (1 / 2 : ℝ) 1)) := by simpa using collar_memLp (dyLp u)
  have hrad := memLp_radialField (by norm_num : (0 : ℝ) < 1 / 2) h1 hI
  have h := representative_weighted_endpoint_estimate (disk_weak_polar u).2.2
    (disk_weak_polar u).2.1 (intervalIntegrable_sliceLp_norm_sq (by norm_num) (by norm_num) hrad)
  change ‖diskTrace u‖ ^ 2 ≤ _ at h
  dsimp [diskProfile, diskRadialProfile] at h
  rw [← integral_annulus_eq_interval_weighted_sliceLp (by norm_num) (by norm_num)
    (collar_memLp (valueCLM u)),
    ← integral_annulus_eq_interval_weighted_sliceLp (by norm_num) (by norm_num) hrad] at h
  have hb := integral_radialField_le (by norm_num : (0 : ℝ) < 1 / 2) h1 hI
  simp only [Dxy_one, Dxy_I] at hb
  linarith

lemma collar_energy_le (f : L2C) :
    (∫ z in annulusSet (1 / 2 : ℝ) 1, ‖f z‖ ^ 2) ≤ ‖f‖ ^ 2 := by
  rw [lp_norm_sq]
  exact setIntegral_mono_set
    ((memLp_two_iff_integrable_sq_norm (Lp.memLp f).aestronglyMeasurable).mp (Lp.memLp f))
    (Filter.Eventually.of_forall (fun z => sq_nonneg _))
    (Filter.Eventually.of_forall collar_subset_disk)

/-- Bound in the adopted disk carrier's actual Hilbert graph norm. -/
theorem diskTrace_norm_sq_le (u : ComplexH1) : ‖diskTrace u‖ ^ 2 ≤ 8 * ‖u‖ ^ 2 := by
  have h := diskTrace_annular_bound u
  rw [integral_add (collar_norm_sq_integrable (dxLp u))
    (collar_norm_sq_integrable (dyLp u))] at h
  have hf := collar_energy_le (valueCLM u)
  have hx := collar_energy_le (dxLp u)
  have hy := collar_energy_le (dyLp u)
  rw [coordinate_graph_norm_sq]
  nlinarith [sq_nonneg ‖dxLp u‖, sq_nonneg ‖dyLp u‖]

lemma diskTrace_norm_le (u : ComplexH1) : ‖diskTrace u‖ ≤ Real.sqrt 8 * ‖u‖ := by
  have h := diskTrace_norm_sq_le u
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)
  have hp : 0 ≤ Real.sqrt 8 * ‖u‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [sq_nonneg (‖diskTrace u‖ - Real.sqrt 8 * ‖u‖)]

/-- The bounded complex-linear trace on the project's genuine weak H¹ disk carrier. -/
def diskTraceCLM : ComplexH1 →L[ℂ] Lp ℂ 2 circleMeasure :=
  LinearMap.mkContinuous
    { toFun := diskTrace
      map_add' := diskTrace_add
      map_smul' := diskTrace_smul }
    (Real.sqrt 8) diskTrace_norm_le

@[simp] lemma diskTraceCLM_apply (u : ComplexH1) : diskTraceCLM u = diskTrace u := rfl

theorem norm_diskTraceCLM_le : ‖diskTraceCLM‖ ≤ Real.sqrt 8 :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) diskTrace_norm_le

end KsIndex.Trace
