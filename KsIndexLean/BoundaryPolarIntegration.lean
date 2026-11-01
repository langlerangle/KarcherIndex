module

public import KsIndexLean.CompactPolarIntegration

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- The support bound for smoothness may extend past the integration annulus.
In particular, this permits tests that do not vanish at the disk boundary. -/
lemma integrableOn_boundaryPolarTest_mul {a b c : ℝ} (ha : 0 < a) (hab : a < b)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a c) (n : ℤ) {f : ℂ → ℂ}
    (hf : MemLp f 2 (volume.restrict (annulusSet a b))) :
    IntegrableOn (fun z => compactPolarTest χ n z * f z) (annulusSet a b) volume := by
  have hpart (H : ℂ → ℝ) (hH : ContDiff ℝ ∞ H) :
      IntegrableOn (fun z => polarTest χ H z • f z) (annulusSet a b) volume := by
    have hp := (contDiff_polarTest ha hχ hs hH).continuous
    obtain ⟨C, hC⟩ := (hasCompactSupport_polarTest hc H).exists_bound_of_continuous hp
    exact integrableOn_bdd_smul ha hab hp.aestronglyMeasurable.restrict
      (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hC z)) hf
  have hr := hpart _ (Complex.reCLM.contDiff.comp (contDiff_fourierAmbient n))
  have hi := hpart _ (Complex.imCLM.contDiff.comp (contDiff_fourierAmbient n))
  apply (hr.add (hi.const_mul Complex.I)).congr
  filter_upwards [] with z
  rw [compactPolarTest_split]
  simp only [Pi.add_apply, Complex.real_smul]
  change (polarTest χ (fun w => (fourierAmbient n w).re) z : ℂ) * f z +
    Complex.I * ((polarTest χ (fun w => (fourierAmbient n w).im) z : ℂ) * f z) = _
  ring

lemma integral_annulus_boundaryPolarTest_conj {a b c : ℝ} (ha : 0 < a) (hab : a < b)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a c) (n : ℤ) {f : ℂ → ℂ}
    (hf : MemLp f 2 (volume.restrict (annulusSet a b))) :
    (∫ z in annulusSet a b, compactPolarTest χ n z * (starRingEnd ℂ) (f z)) =
      ∫ r in Ioo a b, (r * χ r : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ)
          (circleFourierCoeff (sliceLp a b f r) n)) := by
  have hfstar : MemLp (fun z => (starRingEnd ℂ) (f z)) 2
      (volume.restrict (annulusSet a b)) := hf.star
  rw [integral_annulus_compactPolarTest_mul ha χ n _
    (integrableOn_boundaryPolarTest_mul ha hab hχ hc hs n hfstar)]
  apply integral_congr_ae
  filter_upwards [slice_conj_fourier_pairing_ae ha hf n] with r hr
  congr 1
  rw [← hr]
  apply integral_congr_ae
  filter_upwards [] with w
  simp only [sliceFun]
  ring

lemma integral_annulus_boundaryPolarTest_value {a b c : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a c) (n : ℤ) (u : ComplexH1) :
    (∫ z in annulusSet a b, compactPolarTest χ n z * (starRingEnd ℂ) (valueCLM u z)) =
      ∫ r in Ioo a b, (r * χ r : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (interiorDiskMode hab u n r)) := by
  rw [integral_annulus_boundaryPolarTest_conj ha hab hχ hc hs n
    (interiorAnnulus_memLp hb (valueCLM u))]
  apply integral_congr_ae
  filter_upwards [interiorDiskRepresentative_ae ha hab hb u] with r hr
  simp only [interiorDiskMode, circleCoefficientCLM_apply]
  rw [← hr]
  rfl

lemma integral_annulus_boundaryPolarTest_radial {a b c : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a c) (n : ℤ) (u : ComplexH1) :
    (∫ z in annulusSet a b, compactPolarTest χ n z *
      (starRingEnd ℂ) (radialField (Dxy (dxLp u) (dyLp u)) z)) =
      ∫ r in Ioo a b, (r * χ r : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (interiorDiskRadialMode a b u n r)) := by
  have hm : MemLp (radialField (Dxy (dxLp u) (dyLp u))) 2
      (volume.restrict (annulusSet a b)) := by
    apply memLp_radialField ha
    · simpa using interiorAnnulus_memLp hb (dxLp u)
    · simpa using interiorAnnulus_memLp hb (dyLp u)
  simpa only [interiorDiskRadialMode, interiorDiskRadialProfile, circleCoefficientCLM_apply] using
    integral_annulus_boundaryPolarTest_conj ha hab hχ hc hs n hm

lemma integral_annulus_boundaryPolarTest_angular {a b c : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a c) (n : ℤ) (u : ComplexH1) :
    (∫ z in annulusSet a b, compactPolarTest χ n z *
      (starRingEnd ℂ) (angularField (Dxy (dxLp u) (dyLp u)) z)) =
      ∫ r in Ioo a b, (r * χ r : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ)
          (((n : ℂ) * Complex.I) * interiorDiskMode hab u n r)) := by
  rw [integral_annulus_boundaryPolarTest_conj ha hab hχ hc hs n
    (interiorDiskAngularField_memLp hb u)]
  apply integral_congr_ae
  filter_upwards [interior_angular_mode_ae ha hab hb u n] with r hr
  change (r * χ r) • (((2 * Real.pi : ℝ) : ℂ) *
    (starRingEnd ℂ) (circleFourierCoeff (interiorDiskAngularProfile a b u r) n)) = _
  rw [hr]

/-- A radial support bound localizes disk integration to `annulusSet a 1`,
without requiring the cutoff to vanish at radius one. When `a > 0`, this
region is a collar avoiding the centre. -/
lemma integral_disk_boundaryPolarTest_mul {a c : ℝ} {χ : ℝ → ℝ}
    (hs : tsupport χ ⊆ Ioo a c) (n : ℤ) (f : ℂ → ℂ) :
    (∫ z in (disk : Set ℂ), compactPolarTest χ n z * f z) =
      ∫ z in annulusSet a 1, compactPolarTest χ n z * f z := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero disk.isOpen.measurableSet
    (interiorAnnulus_subset_disk le_rfl)
  intro z hz
  have hd : ‖z‖ < 1 := by
    have hball : z ∈ Metric.ball (0 : ℂ) 1 := hz.1
    simpa only [Metric.mem_ball, dist_zero_right] using hball
  have hn : ‖z‖ ∉ tsupport χ := fun h => hz.2 ⟨(hs h).1, hd⟩
  simp [compactPolarTest, image_eq_zero_of_notMem_tsupport hn]

end KsIndex.Trace
