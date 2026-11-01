module

public import KsIndexLean.CompactPolarTests
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section


noncomputable section
open Set MeasureTheory Filter Topology
open scoped ContDiff
namespace KsIndex.Trace

lemma compactPolarTest_radial_derivative {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (n : ℤ) {r : ℝ} (hr : 0 < r) (w : Circle₁) :
    HasDerivAt (fun t : ℝ => compactPolarTest χ n (t • (w : ℂ)))
      (((deriv χ r : ℝ) : ℂ) * fourierAmbient n w) r := by
  have h := ((hχ.differentiable (by simp) r).hasDerivAt.ofReal_comp).mul_const (fourierAmbient n w)
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hr] with t ht
  exact compactPolarTest_slice χ n ht w

lemma compactPolarTest_fderiv_radial {a b : ℝ} (ha : 0 < a) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : tsupport χ ⊆ Ioo a b)
    (n : ℤ) {r : ℝ} (hr : 0 < r) (w : Circle₁) :
    fderiv ℝ (compactPolarTest χ n) (r • (w : ℂ)) w =
      ((deriv χ r : ℝ) : ℂ) * fourierAmbient n w := by
  have hf := ((compactPolarTest_smooth ha hχ hχs n).differentiable (by simp)
    (r • (w : ℂ))).hasFDerivAt
  have hc := hf.comp_hasDerivAt r ((Complex.ofRealCLM.hasDerivAt (x := r)).mul_const (w : ℂ))
  have hd := compactPolarTest_radial_derivative hχ n hr w
  have hc' : HasDerivAt (fun t : ℝ => compactPolarTest χ n (t • (w : ℂ)))
      (fderiv ℝ (compactPolarTest χ n) (r • (w : ℂ)) w) r := by
    convert hc using 1 <;> first | rfl | simp only [Complex.real_smul, Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul]
  exact hc'.unique hd

lemma compactPolarTest_fderiv_angular {a b : ℝ} (ha : 0 < a) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : tsupport χ ⊆ Ioo a b)
    (n : ℤ) (z : ℂ) :
    fderiv ℝ (compactPolarTest χ n) z (z * Complex.I) =
      (n : ℂ) * Complex.I * compactPolarTest χ n z := by
  by_cases hz : z = 0
  · subst z
    simp [compactPolarTest, (phi_norm_zero_near_zero ha hχs).1]
  · have hc := Complex.ofRealCLM.hasFDerivAt.comp z
      ((hχ.differentiable (by simp) ‖z‖).hasFDerivAt.comp z (hasFDerivAt_norm' hz))
    have hh := ((contDiff_fourierAmbient n).differentiable (by simp) (nUnit z)).hasFDerivAt.comp z
      (hasFDerivAt_nUnit hz)
    have hp := hc.mul hh
    change fderiv ℝ (((Complex.ofRealCLM : ℝ → ℂ) ∘ χ ∘ fun w : ℂ => ‖w‖) * (fourierAmbient n ∘ nUnit)) z
      (z * Complex.I) = _
    rw [hp.fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, inner_rotation_zero, smul_eq_mul, mul_zero, map_zero, zero_smul, add_zero,
      ContinuousLinearMap.id_apply]
    rw [← smul_mul_assoc, ← nUnit, angular_fourierAmbient]
    change (χ ‖z‖ : ℂ) * ((n : ℂ) * Complex.I * fourierAmbient n (nUnit z)) = _
    unfold compactPolarTest
    ring

end KsIndex.Trace
