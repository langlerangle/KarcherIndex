module

public import KsIndexLean.KarcherCopyGradientGeometry
public import KsIndexLean.KarcherPolarizedForm

@[expose] public section


/-! The complex gradient pairing from the inverse of the actual first
fundamental form, conjugate-linear in the first scalar-function slot. -/
noncomputable section
namespace KsIndex.KarcherData

/-- Contract the scalar differentials with the inverse Gram matrix. -/
def chartInvMetricGradInner (X : ℂ → AmbientTriple) (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  ((firstFundamentalForm X z Complex.I Complex.I : ℂ) *
      (starRingEnd ℂ) (fderiv ℝ f z 1) * fderiv ℝ g z 1 -
    (firstFundamentalForm X z 1 Complex.I : ℂ) *
      ((starRingEnd ℂ) (fderiv ℝ f z 1) * fderiv ℝ g z Complex.I +
       (starRingEnd ℂ) (fderiv ℝ f z Complex.I) * fderiv ℝ g z 1) +
    (firstFundamentalForm X z 1 1 : ℂ) *
      (starRingEnd ℂ) (fderiv ℝ f z Complex.I) * fderiv ℝ g z Complex.I) /
    (chartGramDet X z : ℂ)

lemma chartInvMetricGradInner_of_conformal {X : ℂ → AmbientTriple} {z : ℂ} {s : ℝ}
    (hs : s ≠ 0) (hm : ∀ d : ℂ, euclideanSq (fderiv ℝ X z d) = s * ‖d‖ ^ 2)
    (f g : ℂ → ℂ) :
    chartInvMetricGradInner X f g z = (s⁻¹ : ℝ) • GradOrtho.gradInner f g z := by
  have hE : firstFundamentalForm X z 1 1 = s := by
    simp only [firstFundamentalForm]; rw [euclideanDot_of_conformal hm]; simp
  have hF : firstFundamentalForm X z 1 Complex.I = 0 := by
    simp only [firstFundamentalForm]; rw [euclideanDot_of_conformal hm]; simp
  have hG : firstFundamentalForm X z Complex.I Complex.I = s := by
    simp only [firstFundamentalForm]; rw [euclideanDot_of_conformal hm]; simp
  simp only [chartInvMetricGradInner, chartGramDet_of_conformal hm, hE, hF, hG,
    GradOrtho.gradInner, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow,
    Complex.ofReal_zero, zero_mul, sub_zero]
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  field_simp

end KsIndex.KarcherData
