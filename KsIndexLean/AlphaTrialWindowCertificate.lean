module

public import KsIndexLean.AlphaTrialWindowSamples
public import KsIndexLean.AlphaTrialLeadingNumeric
public import KsIndexLean.AlphaTrialResidualCertificate

@[expose] public section


/-! Finite numerical obligations for residual-window certification. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ AlphaResidual

/-- Only rational samples and pi remain; the infinite leading tail is replaced
by its independently certified rational center. -/
def windowApproximation (n : ℤ) : ℝ :=
  sigP n * sampleCenter (2*n) + AlphaRemark.spectralUpper^2 *
    (transposeWindowCenter n 16385 + (12/Real.pi) * (-1 : ℝ)^((16385:ℤ)-n) *
      (-98249452881/100000000000000))

def windowApproximationError (n : ℤ) : ℝ :=
  innerError16385 n + sampledResidualRadius AlphaRemark.spectralUpper n 16385 +
    6/1000000000

lemma window_leading_error (n : ℤ) :
    |sampledResidualCenter AlphaRemark.spectralUpper n 16385 - windowApproximation n| ≤
      (6/1000000000 : ℝ) := by
  have hc : AlphaRemark.spectralUpper^2*(12/Real.pi) ≤ (6:ℝ) := by
    rw [← mul_div_assoc, div_le_iff₀ Real.pi_pos]
    norm_num [AlphaRemark.spectralUpper]
    linarith [Real.pi_gt_d20]
  have hc0 : (0:ℝ) ≤ AlphaRemark.spectralUpper^2*(12/Real.pi) := by positivity
  have hh := mul_le_mul_of_nonneg_left leadingTailB_16385_interval hc0
  have hid : sampledResidualCenter AlphaRemark.spectralUpper n 16385 - windowApproximation n =
      (AlphaRemark.spectralUpper^2*(12/Real.pi)) * (-1 : ℝ)^((16385:ℤ)-n) *
        (leadingTailB 16385 - (-98249452881/100000000000000)) := by
    unfold sampledResidualCenter windowApproximation
    ring_nf
  rw [hid, abs_mul, abs_mul, abs_neg_one_zpow, mul_one, abs_of_nonneg hc0]
  exact hh.trans (by nlinarith)

/-- The actual residual is enclosed by the finite sample expression and explicit errors. -/
theorem realResidual_windowApproximation_bound (n : ℤ)
    (hcut : 4*(n:ℝ)^2 < 32771^2) :
    |realResidual AlphaRemark.spectralUpper n - windowApproximation n| ≤
      windowApproximationError n := by
  exact (abs_sub_le _ (sampledResidualCenter AlphaRemark.spectralUpper n 16385) _).trans
    (add_le_add (realResidual_sampledWindow_bound n hcut) (window_leading_error n))

/-- A finite table may supply rational centers and error radii for the window
expression; this theorem then certifies the corresponding weighted residual sum. -/
theorem finite_residual_window_bound (p : Finset ℤ) (a e : ℤ → ℝ)
    (hcut : ∀ n ∈ p, 4*(n:ℝ)^2 < 32771^2)
    (happrox : ∀ n ∈ p, |windowApproximation n - a n| ≤ e n) :
    (∑ n ∈ p, realResidual AlphaRemark.spectralUpper n ^ 2 / residualWeight n) ≤
      ∑ n ∈ p, (|a n|+e n+windowApproximationError n)^2 / residualWeight n := by
  apply Finset.sum_le_sum
  intro n hn
  have hr := realResidual_windowApproximation_bound n (hcut n hn)
  have hh := (abs_sub_le (realResidual AlphaRemark.spectralUpper n) (windowApproximation n) (a n)).trans
    (add_le_add hr (happrox n hn))
  have hb : |realResidual AlphaRemark.spectralUpper n| ≤ |a n|+e n+windowApproximationError n := by
    have ht := abs_add_le (realResidual AlphaRemark.spectralUpper n-a n) (a n)
    rw [sub_add_cancel] at ht
    linarith
  have hb0 : 0 ≤ |a n|+e n+windowApproximationError n := (abs_nonneg _).trans hb
  apply div_le_div_of_nonneg_right _ (residualWeight_pos n).le
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb0).mpr hb

end KsIndex.AlphaRemarkTrial
