module

public import KsIndexLean.FourierEigenTests
public import KsIndexLean.FourierRadialFTC

@[expose] public section


/-! Angular weak identities specialized to the smooth Fourier eigen-tests. -/
noncomputable section
open MeasureTheory Set ComplexConjugate
open scoped ContDiff InnerProductSpace
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma angularTestDeriv_comp_re {F : ℂ → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (z : ℂ) :
    angularTestDeriv (fun w => (F w).re) z = (fderiv ℝ F z (z * Complex.I)).re := by
  have h := Complex.reCLM.hasFDerivAt.comp z (hF.differentiable (by simp) z).hasFDerivAt
  change fderiv ℝ (fun w => Complex.reCLM (F w)) z (z * Complex.I) = _
  exact congrArg (fun A : ℂ →L[ℝ] ℝ => A (z * Complex.I)) h.fderiv

lemma angularTestDeriv_comp_im {F : ℂ → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (z : ℂ) :
    angularTestDeriv (fun w => (F w).im) z = (fderiv ℝ F z (z * Complex.I)).im := by
  have h := Complex.imCLM.hasFDerivAt.comp z (hF.differentiable (by simp) z).hasFDerivAt
  change fderiv ℝ (fun w => Complex.imCLM (F w)) z (z * Complex.I) = _
  exact congrArg (fun A : ℂ →L[ℝ] ℝ => A (z * Complex.I)) h.fderiv

def fourierTestRe (n : ℤ) : ℂ → ℝ := fun z => (fourierAmbient n z).re
def fourierTestIm (n : ℤ) : ℂ → ℝ := fun z => (fourierAmbient n z).im

lemma contDiff_fourierTestRe (n : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (fourierTestRe n) :=
  Complex.reCLM.contDiff.comp (contDiff_fourierAmbient n)
lemma contDiff_fourierTestIm (n : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (fourierTestIm n) :=
  Complex.imCLM.contDiff.comp (contDiff_fourierAmbient n)

def fourierTestLp (n : ℤ) : Lp ℂ 2 circleMeasure :=
  complexAngularTest (fourierTestRe n) (fourierTestIm n)
    (contDiff_fourierTestRe n).continuous (contDiff_fourierTestIm n).continuous

lemma fourierTestLp_coe (n : ℤ) :
    (fourierTestLp n : Circle₁ → ℂ) =ᵐ[circleMeasure] fun w => fourierAmbient n w := by
  filter_upwards [complexAngularTest_coe (fourierTestRe n) (fourierTestIm n)
    (contDiff_fourierTestRe n).continuous (contDiff_fourierTestIm n).continuous] with w hw
  change (complexAngularTest (fourierTestRe n) (fourierTestIm n)
    (contDiff_fourierTestRe n).continuous (contDiff_fourierTestIm n).continuous : Circle₁ → ℂ) w = _
  rw [hw]
  change (fourierAmbient n w).re + Complex.I * (fourierAmbient n w).im = fourierAmbient n w
  rw [mul_comm Complex.I, Complex.re_add_im]

lemma fourierTestLp_eigen (n : ℤ) :
    complexAngularTest (angularTestDeriv (fourierTestRe n)) (angularTestDeriv (fourierTestIm n))
      (contDiff_angularTestDeriv (contDiff_fourierTestRe n)).continuous
      (contDiff_angularTestDeriv (contDiff_fourierTestIm n)).continuous =
      ((n : ℂ) * Complex.I) • fourierTestLp n := by
  apply Lp.ext
  filter_upwards [complexAngularTest_coe
    (angularTestDeriv (fourierTestRe n)) (angularTestDeriv (fourierTestIm n))
    (contDiff_angularTestDeriv (contDiff_fourierTestRe n)).continuous
    (contDiff_angularTestDeriv (contDiff_fourierTestIm n)).continuous,
    Lp.coeFn_smul ((n : ℂ) * Complex.I) (fourierTestLp n), fourierTestLp_coe n]
    with w hl hr hw
  rw [hl, hr, Pi.smul_apply, hw]
  change (angularTestDeriv (fun z => (fourierAmbient n z).re) w : ℂ) +
    Complex.I * (angularTestDeriv (fun z => (fourierAmbient n z).im) w : ℂ) = _
  rw [angularTestDeriv_comp_re (contDiff_fourierAmbient n),
    angularTestDeriv_comp_im (contDiff_fourierAmbient n), mul_comm Complex.I, Complex.re_add_im,
    angular_fourierAmbient]
  rfl

/-- The weak angular identity tested against any integer Fourier mode. -/
theorem disk_fourierTest_pairing_ae (u : ComplexH1) (n : ℤ) :
    ∀ᵐ r ∂volume.restrict (Ioo (1 / 2 : ℝ) 1),
      inner ℂ (fourierTestLp n) (diskAngularProfile u r) =
        ((n : ℂ) * Complex.I) * inner ℂ (fourierTestLp n) (diskProfile u r) :=
  disk_angular_eigentest_ae u (contDiff_fourierTestRe n) (contDiff_fourierTestIm n)
    n (fourierTestLp_eigen n)

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

lemma fourierAmbient_homeomorph (n : ℤ) (x : AddCircle (2 * Real.pi)) :
    fourierAmbient n (fourierCircleHomeomorph x) = fourier n x := by
  induction x using QuotientAddGroup.induction_on with
  | H θ => rw [fourierCircleHomeomorph_coe]; exact fourierAmbient_circleParam n θ

lemma fourierTestLp_toHaar (n : ℤ) :
    angularToHaar (circleL2Equiv (fourierTestLp n)) =
      (fourierLp 2 n : Lp ℂ 2 (AddCircle.haarAddCircle (T := 2 * Real.pi))) := by
  apply Lp.ext
  have ht := measurePreserving_fourierCircleHomeomorph.quasiMeasurePreserving.ae_eq_comp
    (fourierTestLp_coe n)
  have hp := circleL2Equiv_ae (fourierTestLp n)
  rw [angular_ae_eq_haar] at ht hp
  filter_upwards [angularToHaar_ae (circleL2Equiv (fourierTestLp n)), hp, ht,
    coeFn_fourierLp (T := 2 * Real.pi) 2 n] with x ha hb hc hd
  simp only [Function.comp_apply] at hc
  rw [ha, hb, hc, hd]
  exact fourierAmbient_homeomorph n x

/-- Fourier coefficients are normalized pairings for circle measure of mass `2π`. -/
theorem fourierTestLp_inner (n : ℤ) (f : Lp ℂ 2 circleMeasure) :
    ((2 * Real.pi)⁻¹ : ℝ) • inner ℂ (fourierTestLp n) f = circleFourierCoeff f n := by
  rw [← LinearIsometryEquiv.inner_map_map circleL2Equiv, ← inner_angularToHaar,
    fourierTestLp_toHaar]
  have h := (fourierBasis (T := 2 * Real.pi)).repr_apply_apply
    (angularToHaar (circleL2Equiv f)) n
  rw [coe_fourierBasis] at h
  rw [← circleFourierEquiv_apply]
  exact h.symm

/-- The weak angular derivative multiplies Fourier mode `n` by `i n`. -/
theorem disk_angular_fourier_ae (u : ComplexH1) (n : ℤ) :
    ∀ᵐ r ∂volume.restrict (Ioo (1 / 2 : ℝ) 1),
      circleFourierCoeff (diskAngularProfile u r) n =
        ((n : ℂ) * Complex.I) * circleFourierCoeff (diskProfile u r) n := by
  filter_upwards [disk_fourierTest_pairing_ae u n] with r hr
  rw [← fourierTestLp_inner, ← fourierTestLp_inner, hr]
  simp only [Algebra.smul_def]
  ring

end KsIndex.Trace
