module

public import KsIndexLean.DirichletNormalWeakGreen

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

/-- A globally smooth ambient extension of a finite boundary Fourier polynomial. -/
def circleFourierPolynomialAmbient (s : Finset ℤ) (c : ℤ → ℂ) (z : ℂ) : ℂ :=
  ∑ n ∈ s, c n * fourierAmbient n z

lemma circleFourierPolynomialAmbient_smooth (s : Finset ℤ) (c : ℤ → ℂ) :
    ContDiff ℝ ∞ (circleFourierPolynomialAmbient s c) := by
  apply ContDiff.sum
  intro n hn
  exact contDiff_const.mul (contDiff_fourierAmbient n)

lemma circleFourierPolynomialAmbient_circle (s : Finset ℤ) (c : ℤ → ℂ) (w : Circle₁) :
    circleFourierPolynomialAmbient s c w = circleFourierPolynomial s c w :=
  (circleFourierPolynomial_apply s c w).symm

lemma dirichletNormalPolynomial_has_smooth_extension
    (k : ℕ) (lam : ℝ) (u : ComplexH1) (ht : u ∈ zeroTraceDomain Set.univ)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v)) :
    ∃ P : ℂ → ℂ, ContDiff ℝ ∞ P ∧ ∀ w : Circle₁,
      P w = dirichletNormalPolynomial k lam u ht hu w := by
  exact ⟨circleFourierPolynomialAmbient _ _, circleFourierPolynomialAmbient_smooth _ _,
    circleFourierPolynomialAmbient_circle _ _⟩

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
local instance : circleMeasure.IsOpenPosMeasure := by
  rw [← measurePreserving_fourierCircleHomeomorph.map_eq]
  exact fourierCircleHomeomorph.continuous.isOpenPosMeasure_map fourierCircleHomeomorph.surjective

/-- A positive smooth boundary weight can detect every nonzero value of a
continuous flux on the region where that weight is positive. -/
lemma circle_weighted_norm_zero (P : C(Circle₁, ℂ)) (η : Circle₁ → ℝ)
    (hη : Continuous η) (hη0 : ∀ w, 0 ≤ η w)
    (hi : (∫ w, η w * ‖P w‖ ^ 2 ∂circleMeasure) = 0) :
    ∀ w : Circle₁, 0 < η w → P w = 0 := by
  have hc : Continuous (fun w => η w * ‖P w‖ ^ 2) := hη.mul (P.continuous.norm.pow 2)
  have hInt : Integrable (fun w => η w * ‖P w‖ ^ 2) circleMeasure :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have ha := (integral_eq_zero_iff_of_nonneg (fun w => mul_nonneg (hη0 w) (sq_nonneg _)) hInt).mp hi
  have he : (fun w => η w * ‖P w‖ ^ 2) = (fun _ => (0 : ℝ)) :=
    Measure.eq_of_ae_eq ha hc continuous_const
  intro w hw
  have hz := congrFun he w
  have hn : ‖P w‖ ^ 2 = 0 := (mul_eq_zero.mp hz).resolve_left hw.ne'
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (P w)]

end KsIndex.Trace
