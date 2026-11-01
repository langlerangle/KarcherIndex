module

public import KsIndexLean.AlphaLowModeLinear
public import KsIndexLean.AlphaTrialWindowCertificate

@[expose] public section


/-! Direct low-mode residual certificates with all analytic errors restored. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ

def lowResidualCenter (n : ℤ) : ℝ :=
  sigP n * ((sampleNumerator (2*n) : ℝ)/10^51) + AlphaRemark.spectralUpper^2 *
    ((2/Real.pi)*((lowLinearNumerator (Finset.Ico (-16385) 16385) n : ℝ)/10^51) +
      (12/Real.pi)*(-1 : ℝ)^((16385 : ℤ)-n)*(-98249452881/100000000000000))

def lowResidualError (n : ℤ) : ℝ :=
  innerError16385 n + |sigP n| *((sampleRadius (2*n) : ℝ)/10^51) +
    AlphaRemark.spectralUpper^2 *
      ((2/Real.pi)*((lowLinearRadius (Finset.Ico (-16385) 16385) n : ℝ)/10^51) +
        (12/Real.pi)*(1/1000000000))

/-- Concrete integer accumulations enclose the actual residual, with no
uncertified finite or infinite tail omitted. -/
theorem realResidual_lowResidualCenter (n : ℤ)
    (hcut : 4*(n : ℝ)^2 < 32771^2) :
    |realResidual AlphaRemark.spectralUpper n - lowResidualCenter n| ≤
      lowResidualError n := by
  have h1 := mul_le_mul_of_nonneg_left (integer_sample_certificate (2*n)) (abs_nonneg (sigP n))
  rw [← abs_mul, mul_sub] at h1
  have h2 := pairedTranspose_integer_bound n 16385
  have h3 : |(12/Real.pi)*(-1 : ℝ)^((16385 : ℤ)-n)*
      (leadingTailB 16385-(-98249452881/100000000000000))| ≤
      (12/Real.pi)*(1/1000000000) := by
    rw [abs_mul, abs_mul, abs_neg_one_zpow, mul_one,
      abs_of_pos (by positivity : (0 : ℝ) < 12/Real.pi)]
    exact mul_le_mul_of_nonneg_left leadingTailB_16385_interval (by positivity)
  have hh := (abs_add_le _ _).trans (add_le_add h2 h3)
  have hs := mul_le_mul_of_nonneg_left hh (sq_nonneg AlphaRemark.spectralUpper)
  rw [← abs_of_nonneg (sq_nonneg AlphaRemark.spectralUpper), ← abs_mul] at hs
  simp only [abs_sq] at hs
  have hj := (abs_add_le _ _).trans (add_le_add h1 hs)
  have hid : correctedResidualCenter AlphaRemark.spectralUpper n 16385 - lowResidualCenter n =
      (sigP n*sample (2*n)-sigP n*((sampleNumerator (2*n) : ℝ)/10^51)) +
      AlphaRemark.spectralUpper^2 *
        (((∑ t ∈ Finset.range 16385, pairedTransposeTerm n t) -
          (2/Real.pi)*((lowLinearNumerator (Finset.Ico (-16385) 16385) n : ℝ)/10^51)) +
          (12/Real.pi)*(-1 : ℝ)^((16385 : ℤ)-n)*
            (leadingTailB 16385-(-98249452881/100000000000000))) := by
    unfold correctedResidualCenter lowResidualCenter
    rw [trial_eq_sample, Complex.ofReal_re]
    ring
  have hcorrected :
      |correctedResidualCenter AlphaRemark.spectralUpper n 16385 - lowResidualCenter n| ≤
      |sigP n| * ((sampleRadius (2*n) : ℝ)/10^51) +
        AlphaRemark.spectralUpper^2 *
          ((2/Real.pi)*((lowLinearRadius (Finset.Ico (-16385) 16385) n : ℝ)/10^51) +
            (12/Real.pi)*(1/1000000000)) := by
    rw [hid]
    exact hj
  have ht := (abs_sub_le (realResidual AlphaRemark.spectralUpper n)
    (correctedResidualCenter AlphaRemark.spectralUpper n 16385) (lowResidualCenter n)).trans
    (add_le_add (realResidual_inner_certificate n hcut) hcorrected)
  simpa only [lowResidualError, add_assoc] using ht

end KsIndex.AlphaRemarkTrial
