module

public import KsIndexLean.CompactPolarTests
public import KsIndexLean.InteriorAngularFourier

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma integrableOn_compactPolarTest_mul {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a b) (n : ℤ) {f : ℂ → ℂ}
    (hf : MemLp f 2 (volume.restrict (annulusSet a b))) :
    IntegrableOn (fun z => compactPolarTest χ n z * f z) (annulusSet a b) volume := by
  have hr := integrableOn_polarTest_smul ha hab hχ hc hs (Complex.reCLM.contDiff.comp (contDiff_fourierAmbient n)) hf
  have hi := integrableOn_polarTest_smul ha hab hχ hc hs (Complex.imCLM.contDiff.comp (contDiff_fourierAmbient n)) hf
  have h := hr.add (hi.const_mul Complex.I)
  apply h.congr
  filter_upwards [] with z
  rw [compactPolarTest_split]
  simp only [Pi.add_apply, Complex.real_smul]
  change (polarTest χ (fun w => (fourierAmbient n w).re) z : ℂ) * f z +
    Complex.I * ((polarTest χ (fun w => (fourierAmbient n w).im) z : ℂ) * f z) = _
  ring

/-- Polar Fubini for complex Fourier tests, including the radius Jacobian. -/
lemma integral_annulus_compactPolarTest_mul {a b : ℝ} (ha : 0 < a)
    (χ : ℝ → ℝ) (n : ℤ) (f : ℂ → ℂ)
    (hf : IntegrableOn (fun z => compactPolarTest χ n z * f z) (annulusSet a b) volume) :
    (∫ z in annulusSet a b, compactPolarTest χ n z * f z) =
      ∫ r in Ioo a b, (r * χ r : ℝ) •
        (∫ w : Circle₁, fourierAmbient n w * sliceFun f r w ∂circleMeasure) := by
  rw [integral_annulus_eq_weighted ha hf.aestronglyMeasurable,
    MeasureTheory.integral_prod _ (integrable_weighted_pullback ha hf)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with w
  change r • (compactPolarTest χ n (r • (w : ℂ)) * f (r • (w : ℂ))) = _
  rw [compactPolarTest_slice χ n (ha.trans hr.1)]
  simp only [sliceFun, Complex.real_smul, Complex.ofReal_mul]
  ring

lemma integral_compactPolarTest_mul {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a b) (n : ℤ) {f : ℂ → ℂ}
    (hf : MemLp f 2 (volume.restrict (annulusSet a b))) :
    (∫ z, compactPolarTest χ n z * f z) =
      ∫ r in Ioo a b, (r * χ r : ℝ) •
        (∫ w : Circle₁, fourierAmbient n w * sliceFun f r w ∂circleMeasure) := by
  rw [← integral_annulus_compactPolarTest_mul ha χ n f
    (integrableOn_compactPolarTest_mul ha hab hχ hc hs n hf)]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  rw [image_eq_zero_of_notMem_tsupport (fun hm => hz (compactPolarTest_annular_support hs n hm)),
    zero_mul]

/-- Integrating a compact Fourier test extracts the conjugate coefficient
with the geometric circle normalization and the radial Jacobian. -/
lemma integral_compactPolarTest_conj {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a b) (n : ℤ) {f : ℂ → ℂ}
    (hf : MemLp f 2 (volume.restrict (annulusSet a b))) :
    (∫ z, compactPolarTest χ n z * (starRingEnd ℂ) (f z)) =
      ∫ r in Ioo a b, (r * χ r : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ)
          (circleFourierCoeff (sliceLp a b f r) n)) := by
  have hfstar : MemLp (fun z => (starRingEnd ℂ) (f z)) 2
      (volume.restrict (annulusSet a b)) := hf.star
  rw [integral_compactPolarTest_mul ha hab hχ hc hs n hfstar]
  apply integral_congr_ae
  filter_upwards [slice_conj_fourier_pairing_ae ha hf n] with r hr
  congr 1
  rw [← hr]
  apply integral_congr_ae
  filter_upwards [] with w
  simp only [sliceFun]
  ring

lemma integral_compactPolarTest_value {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a b) (n : ℤ) (u : KsIndex.WeakH1.ComplexH1) :
    (∫ z, compactPolarTest χ n z * (starRingEnd ℂ) (KsIndex.WeakH1.valueCLM u z)) =
      ∫ r in Ioo a b, (r * χ r : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (interiorDiskMode hab u n r)) := by
  rw [integral_compactPolarTest_conj ha hab hχ hc hs n
    (interiorAnnulus_memLp hb (KsIndex.WeakH1.valueCLM u))]
  apply integral_congr_ae
  filter_upwards [interiorDiskRepresentative_ae ha hab hb u] with r hr
  simp only [interiorDiskMode, circleCoefficientCLM_apply]
  rw [← hr]
  rfl

lemma integral_compactPolarTest_radial {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a b) (n : ℤ) (u : ComplexH1) :
    (∫ z, compactPolarTest χ n z *
      (starRingEnd ℂ) (radialField (Dxy (dxLp u) (dyLp u)) z)) =
      ∫ r in Ioo a b, (r * χ r : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (interiorDiskRadialMode a b u n r)) := by
  have hm : MemLp (radialField (Dxy (dxLp u) (dyLp u))) 2
      (volume.restrict (annulusSet a b)) := by
    apply memLp_radialField ha
    · simpa using interiorAnnulus_memLp hb (dxLp u)
    · simpa using interiorAnnulus_memLp hb (dyLp u)
  simpa only [interiorDiskRadialMode, interiorDiskRadialProfile, circleCoefficientCLM_apply] using
    integral_compactPolarTest_conj ha hab hχ hc hs n hm

lemma integral_compactPolarTest_angular {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a b) (n : ℤ) (u : ComplexH1) :
    (∫ z, compactPolarTest χ n z *
      (starRingEnd ℂ) (angularField (Dxy (dxLp u) (dyLp u)) z)) =
      ∫ r in Ioo a b, (r * χ r : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ)
          (((n : ℂ) * Complex.I) * interiorDiskMode hab u n r)) := by
  rw [integral_compactPolarTest_conj ha hab hχ hc hs n
    (interiorDiskAngularField_memLp hb u)]
  apply integral_congr_ae
  filter_upwards [interior_angular_mode_ae ha hab hb u n] with r hr
  change (r * χ r) • (((2 * Real.pi : ℝ) : ℂ) *
    (starRingEnd ℂ) (circleFourierCoeff (interiorDiskAngularProfile a b u r) n)) = _
  rw [hr]

end KsIndex.Trace
