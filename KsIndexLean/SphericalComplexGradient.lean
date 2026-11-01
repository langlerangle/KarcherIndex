module

public import KsIndexLean.SphericalGradientLift
public import KsIndexLean.WeakH1Adapter

@[expose] public section


noncomputable section
namespace KsIndex.Spherical

/-- Real and imaginary tangent gradients of a complex chart derivative. -/
def complexGradientLift (z a b : ℂ) : Ambient × Ambient :=
  (gradientLift z (Complex.mk a.re b.re), gradientLift z (Complex.mk a.im b.im))

/-- Hermitian tangent pairing, conjugate-linear in its first argument. -/
def tangentPair (U V : Ambient × Ambient) : ℂ :=
  (inner ℝ U.1 V.1 : ℂ) + (inner ℝ U.2 V.2 : ℂ) +
    Complex.I * ((inner ℝ U.1 V.2 : ℂ) - (inner ℝ U.2 V.1 : ℂ))

lemma complexGradientLift_represents (z a b w : ℂ) :
    (inner ℝ (complexGradientLift z a b).1 (fderiv ℝ stereoPoint z w) : ℂ) +
      Complex.I * (inner ℝ (complexGradientLift z a b).2
        (fderiv ℝ stereoPoint z w) : ℂ) = w.re • a + w.im • b := by
  simp only [complexGradientLift, gradientLift_represents]
  apply Complex.ext <;> simp [Complex.real_smul]

lemma complexGradientLift_pair_cancel (z a b c d : ℂ) :
    (stereoAreaDensity z : ℂ) * tangentPair (complexGradientLift z a b)
      (complexGradientLift z c d) = (starRingEnd ℂ) a * c + (starRingEnd ℂ) b * d := by
  have h (v w : ℂ) : (stereoAreaDensity z : ℂ) *
      (inner ℝ (gradientLift z v) (gradientLift z w) : ℂ) = (inner ℝ v w : ℂ) := by
    rw [← Complex.ofReal_mul, gradientLift_inner_cancel]
  simp only [tangentPair, complexGradientLift]
  rw [mul_add, mul_add, mul_left_comm _ Complex.I, mul_sub, h, h, h, h]
  apply Complex.ext <;> simp <;> ring

end KsIndex.Spherical
