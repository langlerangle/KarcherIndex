module

public import KsIndexLean.TraceFourierSummability

@[expose] public section


/-! Control of trace collar energies by the adopted disk H1 graph norm. -/
noncomputable section
open MeasureTheory Set
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma collar_slice_energy_le {f : ℂ → ℂ}
    (hf : MemLp f 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 1))) :
    (∫ r in (1 / 2 : ℝ)..1, ‖sliceLp (1 / 2) 1 f r‖ ^ 2) ≤
      2 * ∫ z in annulusSet (1 / 2 : ℝ) 1, ‖f z‖ ^ 2 := by
  have hi := intervalIntegrable_sliceLp_norm_sq (by norm_num) (by norm_num) hf
  have h := weight_double hi (hi.continuousOn_mul continuousOn_id) (fun r _ => sq_nonneg _)
  rw [← integral_annulus_eq_interval_weighted_sliceLp (by norm_num) (by norm_num) hf] at h
  exact h

lemma diskProfile_energy_le (u : ComplexH1) :
    (∫ r in (1 / 2 : ℝ)..1, ‖diskProfile u r‖ ^ 2) ≤ 2 * ‖valueCLM u‖ ^ 2 :=
  (collar_slice_energy_le (collar_memLp (valueCLM u))).trans
    (mul_le_mul_of_nonneg_left (collar_energy_le (valueCLM u)) (by norm_num))

lemma diskRadialProfile_energy_le (u : ComplexH1) :
    (∫ r in (1 / 2 : ℝ)..1, ‖diskRadialProfile u r‖ ^ 2) ≤
      4 * (‖dxLp u‖ ^ 2 + ‖dyLp u‖ ^ 2) := by
  have h1 : MemLp (fun z => Dxy (dxLp u) (dyLp u) z 1) 2
      (volume.restrict (annulusSet (1 / 2 : ℝ) 1)) := by simpa using collar_memLp (dxLp u)
  have hI : MemLp (fun z => Dxy (dxLp u) (dyLp u) z Complex.I) 2
      (volume.restrict (annulusSet (1 / 2 : ℝ) 1)) := by simpa using collar_memLp (dyLp u)
  have h := collar_slice_energy_le (memLp_radialField (by norm_num : (0 : ℝ) < 1 / 2) h1 hI)
  have hr := integral_radialField_le (by norm_num : (0 : ℝ) < 1 / 2) h1 hI
  simp only [Dxy_one, Dxy_I] at hr
  rw [integral_add (collar_norm_sq_integrable (dxLp u)) (collar_norm_sq_integrable (dyLp u))] at hr
  change (∫ r in (1 / 2 : ℝ)..1, ‖diskRadialProfile u r‖ ^ 2) ≤ _ at h
  have hx := collar_energy_le (dxLp u)
  have hy := collar_energy_le (dyLp u)
  linarith

lemma angularField_sq_le_collar (u : ComplexH1) {z : ℂ}
    (hz : z ∈ annulusSet (1 / 2 : ℝ) 1) :
    ‖angularField (Dxy (dxLp u) (dyLp u)) z‖ ^ 2 ≤
      2 * (‖dxLp u z‖ ^ 2 + ‖dyLp u z‖ ^ 2) := by
  have hi : |z.im| ≤ 1 := (Complex.abs_im_le_norm z).trans hz.2.le
  have hr : |z.re| ≤ 1 := (Complex.abs_re_le_norm z).trans hz.2.le
  have hn := norm_add_le ((-z.im) • dxLp u z) (z.re • dyLp u z)
  have he : angularField (Dxy (dxLp u) (dyLp u)) z =
      (-z.im) • dxLp u z + z.re • dyLp u z := by simp [angularField]
  rw [he]
  simp only [norm_smul, Real.norm_eq_abs, abs_neg] at hn
  have ha := mul_le_mul_of_nonneg_right hi (norm_nonneg (dxLp u z))
  have hb := mul_le_mul_of_nonneg_right hr (norm_nonneg (dyLp u z))
  have hsum : ‖(-z.im) • dxLp u z + z.re • dyLp u z‖ ≤ ‖dxLp u z‖ + ‖dyLp u z‖ := by linarith
  have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hsum
  nlinarith [sq_nonneg (‖dxLp u z‖ - ‖dyLp u z‖)]

lemma diskAngularProfile_energy_le (u : ComplexH1) :
    (∫ r in (1 / 2 : ℝ)..1, ‖diskAngularProfile u r‖ ^ 2) ≤
      4 * (‖dxLp u‖ ^ 2 + ‖dyLp u‖ ^ 2) := by
  have h := collar_slice_energy_le (diskAngularField_memLp u)
  have hi := (memLp_two_iff_integrable_sq_norm
    (diskAngularField_memLp u).aestronglyMeasurable).mp (diskAngularField_memLp u)
  have hb := integral_mono_ae hi
    (((collar_norm_sq_integrable (dxLp u)).add (collar_norm_sq_integrable (dyLp u))).const_mul 2)
    (by
      filter_upwards [ae_restrict_mem measurableSet_annulusSet] with z hz
      exact angularField_sq_le_collar u hz)
  simp only [Pi.add_apply] at hb
  rw [integral_const_mul, integral_add (collar_norm_sq_integrable (dxLp u))
    (collar_norm_sq_integrable (dyLp u))] at hb
  change (∫ r in (1 / 2 : ℝ)..1, ‖diskAngularProfile u r‖ ^ 2) ≤ _ at h
  have hx := collar_energy_le (dxLp u)
  have hy := collar_energy_le (dyLp u)
  linarith

/-- Quantitative half-order trace bound in the adopted H1 graph norm. -/
theorem diskTrace_half_weight_tsum_le (u : ComplexH1) :
    (∑' n : ℤ, (1 + |(n : ℝ)|) * ‖circleFourierCoeff (diskTraceCLM u) n‖ ^ 2) ≤
      (36 * (2 * Real.pi)⁻¹) * ‖u‖ ^ 2 := by
  apply Real.tsum_le_of_sum_le (fun n => by positivity)
  intro F
  have h := diskTrace_finite_half_weight_le u F
  have hp : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  have hv := mul_le_mul_of_nonneg_left (diskProfile_energy_le u) hp
  have ha := mul_le_mul_of_nonneg_left (diskAngularProfile_energy_le u) hp
  have hr := mul_le_mul_of_nonneg_left (diskRadialProfile_energy_le u) hp
  rw [coordinate_graph_norm_sq]
  nlinarith [mul_nonneg hp (sq_nonneg ‖valueCLM u‖)]

end KsIndex.Trace
