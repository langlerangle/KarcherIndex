module

public import KsIndexLean.AngularPairingAE

@[expose] public section


/-! Complex angular tests from the real weak angular identity. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff InnerProductSpace
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- A complex angular test assembled from its two real components. -/
def complexAngularTest (H J : ℂ → ℝ) (hH : Continuous H) (hJ : Continuous J) :
    Lp ℂ 2 circleMeasure :=
  ContinuousMap.toLp 2 circleMeasure ℂ (realAngularMap H hH) +
    Complex.I • ContinuousMap.toLp 2 circleMeasure ℂ (realAngularMap J hJ)

theorem complexAngularTest_coe (H J : ℂ → ℝ) (hH : Continuous H) (hJ : Continuous J) :
    (complexAngularTest H J hH hJ : Circle₁ → ℂ) =ᵐ[circleMeasure]
      fun w => (H w : ℂ) + Complex.I * (J w : ℂ) := by
  filter_upwards [Lp.coeFn_add
      (ContinuousMap.toLp 2 circleMeasure ℂ (realAngularMap H hH))
      (Complex.I • ContinuousMap.toLp 2 circleMeasure ℂ (realAngularMap J hJ)),
    Lp.coeFn_smul Complex.I (ContinuousMap.toLp 2 circleMeasure ℂ (realAngularMap J hJ)),
    ContinuousMap.coeFn_toLp (p := 2) (μ := circleMeasure) (𝕜 := ℂ) (realAngularMap H hH),
    ContinuousMap.coeFn_toLp (p := 2) (μ := circleMeasure) (𝕜 := ℂ) (realAngularMap J hJ)]
    with w ha hs hH' hJ'
  change (ContinuousMap.toLp 2 circleMeasure ℂ (realAngularMap H hH) +
    Complex.I • ContinuousMap.toLp 2 circleMeasure ℂ (realAngularMap J hJ) : Lp ℂ 2 circleMeasure) w = _
  rw [ha, Pi.add_apply, hs, Pi.smul_apply, hH', hJ']
  rfl

/-- The real weak angular identities imply their complex counterpart, with
conjugation in the first slot retained. -/
theorem disk_complex_angular_pairing_ae (u : ComplexH1) {H J : ℂ → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hJ : ContDiff ℝ (⊤ : ℕ∞) J) :
    ∀ᵐ t ∂volume.restrict (Ioo (1 / 2 : ℝ) 1),
      inner ℂ (complexAngularTest (angularTestDeriv H) (angularTestDeriv J)
        (contDiff_angularTestDeriv hH).continuous (contDiff_angularTestDeriv hJ).continuous)
        (diskProfile u t) =
      -inner ℂ (complexAngularTest H J hH.continuous hJ.continuous)
        (diskAngularProfile u t) := by
  filter_upwards [disk_angular_profile_pairing_ae u hH,
    disk_angular_profile_pairing_ae u hJ] with t htH htJ
  simp only [complexAngularTest, inner_add_left, inner_smul_left, htH, htJ]
  ring

/-- A smooth angular eigen-test transfers the angular derivative to its Fourier
pairing with the weak disk profile. -/
theorem disk_angular_eigentest_ae (u : ComplexH1) {H J : ℂ → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hJ : ContDiff ℝ (⊤ : ℕ∞) J)
    (n : ℤ)
    (he : complexAngularTest (angularTestDeriv H) (angularTestDeriv J)
        (contDiff_angularTestDeriv hH).continuous (contDiff_angularTestDeriv hJ).continuous =
      ((n : ℂ) * Complex.I) • complexAngularTest H J hH.continuous hJ.continuous) :
    ∀ᵐ t ∂volume.restrict (Ioo (1 / 2 : ℝ) 1),
      inner ℂ (complexAngularTest H J hH.continuous hJ.continuous)
        (diskAngularProfile u t) =
      ((n : ℂ) * Complex.I) *
        inner ℂ (complexAngularTest H J hH.continuous hJ.continuous) (diskProfile u t) := by
  filter_upwards [disk_complex_angular_pairing_ae u hH hJ] with t ht
  rw [he, inner_smul_left] at ht
  simp only [map_mul, map_intCast, Complex.conj_I] at ht
  linear_combination ht

end KsIndex.Trace
