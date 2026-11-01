module

public import KsIndexLean.AlphaTrialInnerNumeric
public import KsIndexLean.AlphaRemarkEndpoints

@[expose] public section


/-! A rational pointwise truncation error for the fixed threshold trial. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open AlphaResidual

/-- This expression is rational at every integer residual index. -/
def innerError16385 (n : ℤ) : ℝ :=
  innerPairAMajorant n 32771*(31/1000000000) +
    innerPairBMajorant n 32771*(7/10000000000000)

lemma innerError16385_nonneg (n : ℤ) (hcut : 4*(n:ℝ)^2 < 32771^2) :
    0 ≤ innerError16385 n := by
  have hd : 0 < (32771:ℝ)^2-4*(n:ℝ)^2 := by linarith
  unfold innerError16385 innerPairAMajorant innerPairBMajorant
  positivity

/-- The finite corrected residual center has an explicit rational error envelope. -/
theorem realResidual_inner_certificate (n : ℤ) (hcut : 4*(n:ℝ)^2 < 32771^2) :
    |realResidual AlphaRemark.spectralUpper n -
      correctedResidualCenter AlphaRemark.spectralUpper n 16385| ≤ innerError16385 n := by
  have hd : 0 < (32771:ℝ)^2-4*(n:ℝ)^2 := by linarith
  have ha : 0 ≤ innerPairAMajorant n 32771 := by
    unfold innerPairAMajorant
    positivity
  have hb : 0 ≤ innerPairBMajorant n 32771 := by
    unfold innerPairBMajorant
    positivity
  have hc0 : (0:ℝ) ≤ AlphaRemark.spectralUpper^2*(2/Real.pi) := by positivity
  have hc1 : AlphaRemark.spectralUpper^2*(2/Real.pi) ≤ (1:ℝ) := by
    rw [← mul_div_assoc, div_le_iff₀ Real.pi_pos]
    norm_num [AlphaRemark.spectralUpper]
    linarith [Real.pi_gt_d20]
  have hh := realResidual_finite_endpoint_error AlphaRemark.spectralUpper n 16385
    (by norm_num) (by norm_num at hcut ⊢; exact hcut)
  norm_num only [Nat.cast_ofNat] at hh
  have hmajor := add_le_add (mul_le_mul_of_nonneg_left trialInnerUA_16385 ha)
    (mul_le_mul_of_nonneg_left trialInnerUB_16385 hb)
  calc
    _ ≤ AlphaRemark.spectralUpper^2*(2/Real.pi)*
        (innerPairAMajorant n 32771*trialInnerUA 16385 +
          innerPairBMajorant n 32771*trialInnerUB 16385) := by convert hh using 1
    _ ≤ AlphaRemark.spectralUpper^2*(2/Real.pi)*innerError16385 n :=
      mul_le_mul_of_nonneg_left hmajor hc0
    _ ≤ innerError16385 n := mul_le_of_le_one_left (innerError16385_nonneg n hcut) hc1

end KsIndex.AlphaRemarkTrial
