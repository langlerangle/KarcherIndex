module

public import KsIndexLean.KarcherLocalPrimitive
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

@[expose] public section


/-! Real differentials of the local representatives of the actual EW integral.
The target triples use an explicit Euclidean quadratic form, not the product sup norm. -/
noncomputable section
namespace KsIndex.KarcherData

/-- Real part of multiplication by a complex differential coefficient. -/
def realCoeffLinear (a : ℂ) : ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp (((1 : ℂ →L[ℂ] ℂ).smulRight a).restrictScalars ℝ)

@[simp] lemma realCoeffLinear_apply (a d : ℂ) : realCoeffLinear a d = (d * a).re := rfl

/-- The real differential prescribed by the normalized EW coefficients. -/
def ewRealDifferential (k : ℕ) (w : ℂ) : ℂ →L[ℝ] (ℝ × ℝ × ℝ) :=
  (realCoeffLinear (coeff1 k w)).prod
    ((realCoeffLinear (coeff2 k w)).prod (realCoeffLinear (coeff3 k w)))

/-- A real local representative; its quotient is linked to the descended map below. -/
def realPrimitive (F₁ F₂ F₃ : ℂ → ℂ) (w : ℂ) : ℝ × ℝ × ℝ :=
  ((F₁ w).re, (F₂ w).re, (F₃ w).re)

lemma hasFDerivAt_realPrimitive {k : ℕ} {w : ℂ} {F₁ F₂ F₃ : ℂ → ℂ}
    (h₁ : HasDerivAt F₁ (coeff1 k w) w)
    (h₂ : HasDerivAt F₂ (coeff2 k w) w)
    (h₃ : HasDerivAt F₃ (coeff3 k w) w) :
    HasFDerivAt (realPrimitive F₁ F₂ F₃) (ewRealDifferential k w) w := by
  exact (Complex.reCLM.hasFDerivAt.comp w (h₁.hasFDerivAt.restrictScalars ℝ)).prodMk
    ((Complex.reCLM.hasFDerivAt.comp w (h₂.hasFDerivAt.restrictScalars ℝ)).prodMk
      (Complex.reCLM.hasFDerivAt.comp w (h₃.hasFDerivAt.restrictScalars ℝ)))

/-- Euclidean squared length, independent of the norm instance on a product. -/
def euclideanSq (v : ℝ × ℝ × ℝ) : ℝ := v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2

lemma ewRealDifferential_metric {k : ℕ} (hk : 2 ≤ k) (w d : ℂ) :
    euclideanSq (ewRealDifferential k w d) = Surface.rho k w ^ 2 * ‖d‖ ^ 2 := by
  have he := Weierstrass.weierstrass_equal_lengths (gauss k w) (etaTarget k w)
  have ho := Weierstrass.weierstrass_orthogonal (gauss k w) (etaTarget k w)
  change Weierstrass.realSq (coeff1 k w) (coeff2 k w) (coeff3 k w) =
    Weierstrass.imagSq (coeff1 k w) (coeff2 k w) (coeff3 k w) at he
  change Weierstrass.realImagDot (coeff1 k w) (coeff2 k w) (coeff3 k w) = 0 at ho
  rw [← real_metric_eq_rho_sq hk w, Complex.sq_norm]
  simp only [euclideanSq, ewRealDifferential, ContinuousLinearMap.prod_apply,
    realCoeffLinear_apply, Complex.mul_re, Complex.normSq_apply,
    Weierstrass.realSq, Weierstrass.imagSq, Weierstrass.realImagDot] at *
  change _ = ((coeff1 k w).re ^ 2 + (coeff2 k w).re ^ 2 +
    (coeff3 k w).re ^ 2) * (d.re * d.re + d.im * d.im)
  linear_combination -(d.im ^ 2) * he - 2 * d.re * d.im * ho

/-- Non-punctures have a positive definite induced quadratic form. -/
lemma ewRealDifferential_metric_pos {k : ℕ} (hk : 2 ≤ k) {w d : ℂ}
    (hw : w ∉ Surface.punctures k) (hd : d ≠ 0) :
    0 < euclideanSq (ewRealDifferential k w d) := by
  rw [ewRealDifferential_metric hk]
  have hp := Weierstrass.weierstrass_metric_pos (gauss k w) (etaTarget k w)
    (etaTarget_ne_zero hk hw)
  rw [real_metric_eq_rho_sq hk] at hp
  exact mul_pos hp (sq_pos_of_pos (norm_pos_iff.mpr hd))

lemma ewRealDifferential_injective {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : w ∉ Surface.punctures k) : Function.Injective (ewRealDifferential k w) := by
  intro d e he
  have hzero : ewRealDifferential k w (d - e) = 0 := by
    rw [map_sub, he, sub_self]
  by_contra hne
  have hp := ewRealDifferential_metric_pos hk hw (sub_ne_zero.mpr hne)
  simp [hzero, euclideanSq] at hp

/-- Actual local representatives have the EW differential and no rank loss.
This is a finite-chart statement; it does not assert global embeddedness. -/
theorem exists_local_real_representative {k : ℕ} (hk : 2 ≤ k)
    (b x : PuncturedPlane k) :
    ∃ r : ℝ, 0 < r ∧ ∃ X : ℂ → ℝ × ℝ × ℝ,
      X x.val = 0 ∧
      (∀ z ∈ Metric.ball x.val r, HasFDerivAt X (ewRealDifferential k z) z) ∧
      (∀ y : PuncturedPlane k, y.val ∈ Metric.ball x.val r →
        descendedIntegral hk b y = descendedIntegral hk b x + projectPeriod (X y.val)) ∧
      Function.Injective (ewRealDifferential k x.val) := by
  obtain ⟨r, hr, F₁, F₂, F₃, hF₁, hF₂, hF₃, h₁, h₂, h₃, hrepr⟩ :=
    exists_local_primitives hk b x
  refine ⟨r, hr, realPrimitive F₁ F₂ F₃, ?_, ?_, hrepr,
    ewRealDifferential_injective hk x.property⟩
  · simp [realPrimitive, hF₁, hF₂, hF₃]
  · intro z hz
    exact hasFDerivAt_realPrimitive (h₁ z hz) (h₂ z hz) (h₃ z hz)

end KsIndex.KarcherData
