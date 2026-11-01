module

public import KsIndexLean.AngularFourierIdentity
public import KsIndexLean.PolarFourierPairing

@[expose] public section


/-! Angular Fourier differentiation on every interior annulus. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff InnerProductSpace
namespace KsIndex.Trace
open KsIndex.WeakH1

def interiorDiskAngularProfile (a b : ℝ) (u : ComplexH1) :=
  sliceLp a b (angularField (Dxy (dxLp u) (dyLp u)))

lemma interiorDiskAngularField_memLp {a b : ℝ} (hb : b ≤ 1) (u : ComplexH1) :
    MemLp (angularField (Dxy (dxLp u) (dyLp u))) 2
      (volume.restrict (annulusSet a b)) := by
  apply memLp_angularField
  · simpa using interiorAnnulus_memLp hb (dxLp u)
  · simpa using interiorAnnulus_memLp hb (dyLp u)

theorem interior_angular_pairing_ae {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (u : ComplexH1) {H : ℂ → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      (∫ w : Circle₁, angularTestDeriv H w • sliceFun (valueCLM u) t w ∂circleMeasure) =
        -∫ w : Circle₁, H w •
          sliceFun (angularField (Dxy (dxLp u) (dyLp u))) t w ∂circleMeasure := by
  apply angular_pairing_ae ha hab hH
    ((carrier_hasJet u).mono (interiorAnnulus_subset_disk hb)) (interiorAnnulus_memLp hb (valueCLM u))
  · simpa using interiorAnnulus_memLp hb (dxLp u)
  · simpa using interiorAnnulus_memLp hb (dyLp u)

/-- The same fixed-test identity on the actual L²-valued disk profiles. -/
theorem interior_angular_profile_pairing_ae {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (u : ComplexH1) {H : ℂ → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      inner ℂ (ContinuousMap.toLp 2 circleMeasure ℂ
        (realAngularMap (angularTestDeriv H) (contDiff_angularTestDeriv hH).continuous))
        (interiorDiskProfile a b u t) =
      -inner ℂ (ContinuousMap.toLp 2 circleMeasure ℂ (realAngularMap H hH.continuous))
        (interiorDiskAngularProfile a b u t) := by
  filter_upwards [interior_angular_pairing_ae ha hab hb u hH,
    realAngular_pairing_ae ha (interiorAnnulus_memLp hb (valueCLM u))
      (angularTestDeriv H) (contDiff_angularTestDeriv hH).continuous,
    realAngular_pairing_ae ha (interiorDiskAngularField_memLp hb u)
      H hH.continuous] with t ht hl hr
  exact hl.trans (ht.trans (congrArg Neg.neg hr.symm))

theorem interior_complex_angular_pairing_ae {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (u : ComplexH1) {H J : ℂ → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hJ : ContDiff ℝ (⊤ : ℕ∞) J) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      inner ℂ (complexAngularTest (angularTestDeriv H) (angularTestDeriv J)
        (contDiff_angularTestDeriv hH).continuous (contDiff_angularTestDeriv hJ).continuous)
        (interiorDiskProfile a b u t) =
      -inner ℂ (complexAngularTest H J hH.continuous hJ.continuous)
        (interiorDiskAngularProfile a b u t) := by
  filter_upwards [interior_angular_profile_pairing_ae ha hab hb u hH,
    interior_angular_profile_pairing_ae ha hab hb u hJ] with t htH htJ
  simp only [complexAngularTest, inner_add_left, inner_smul_left, htH, htJ]
  ring

/-- A smooth angular eigen-test transfers the angular derivative to its Fourier
pairing with the weak disk profile. -/
theorem interior_angular_eigentest_ae {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (u : ComplexH1) {H J : ℂ → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hJ : ContDiff ℝ (⊤ : ℕ∞) J)
    (n : ℤ)
    (he : complexAngularTest (angularTestDeriv H) (angularTestDeriv J)
        (contDiff_angularTestDeriv hH).continuous (contDiff_angularTestDeriv hJ).continuous =
      ((n : ℂ) * Complex.I) • complexAngularTest H J hH.continuous hJ.continuous) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      inner ℂ (complexAngularTest H J hH.continuous hJ.continuous)
        (interiorDiskAngularProfile a b u t) =
      ((n : ℂ) * Complex.I) *
        inner ℂ (complexAngularTest H J hH.continuous hJ.continuous) (interiorDiskProfile a b u t) := by
  filter_upwards [interior_complex_angular_pairing_ae ha hab hb u hH hJ] with t ht
  rw [he, inner_smul_left] at ht
  simp only [map_mul, map_intCast, Complex.conj_I] at ht
  linear_combination ht

theorem interior_fourierTest_pairing_ae {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (u : ComplexH1) (n : ℤ) :
    ∀ᵐ r ∂volume.restrict (Ioo a b),
      inner ℂ (fourierTestLp n) (interiorDiskAngularProfile a b u r) =
        ((n : ℂ) * Complex.I) * inner ℂ (fourierTestLp n) (interiorDiskProfile a b u r) :=
  interior_angular_eigentest_ae ha hab hb u (contDiff_fourierTestRe n) (contDiff_fourierTestIm n)
    n (fourierTestLp_eigen n)

theorem interior_angular_fourier_ae {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (u : ComplexH1) (n : ℤ) :
    ∀ᵐ r ∂volume.restrict (Ioo a b),
      circleFourierCoeff (interiorDiskAngularProfile a b u r) n =
        ((n : ℂ) * Complex.I) * circleFourierCoeff (interiorDiskProfile a b u r) n := by
  filter_upwards [interior_fourierTest_pairing_ae ha hab hb u n] with r hr
  rw [← fourierTestLp_inner, ← fourierTestLp_inner, hr]
  simp only [Algebra.smul_def]
  ring

/-- The continuous radial representative has the same angular multiplier. -/
theorem interior_angular_mode_ae {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (u : ComplexH1) (n : ℤ) :
    ∀ᵐ r ∂volume.restrict (Ioo a b),
      circleFourierCoeff (interiorDiskAngularProfile a b u r) n =
        ((n : ℂ) * Complex.I) * interiorDiskMode hab u n r := by
  filter_upwards [interior_angular_fourier_ae ha hab hb u n,
    interiorDiskRepresentative_ae ha hab hb u] with r hr he
  rw [hr, he]
  simp only [interiorDiskMode, circleCoefficientCLM_apply]

/-- Raw angular slices paired with a Fourier test, ready for polar integration. -/
theorem interiorDiskAngularMode_pairing_ae {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (u : ComplexH1) (n : ℤ) :
    ∀ᵐ r ∂volume.restrict (Ioo a b),
      (∫ w : Circle₁, star (sliceFun (angularField (Dxy (dxLp u) (dyLp u))) r w) *
        fourierAmbient n w ∂circleMeasure) =
      ((2 * Real.pi : ℝ) : ℂ) * star (((n : ℂ) * Complex.I) * interiorDiskMode hab u n r) := by
  filter_upwards [slice_conj_fourier_pairing_ae ha (interiorDiskAngularField_memLp hb u) n,
    interior_angular_mode_ae ha hab hb u n] with r hr he
  exact hr.trans (congrArg (fun z : ℂ => ((2 * Real.pi : ℝ) : ℂ) * star z) he)

end KsIndex.Trace
