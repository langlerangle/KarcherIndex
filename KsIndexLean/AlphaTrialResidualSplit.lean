module

public import KsIndexLean.AlphaTrialRealResidual
public import KsIndexLean.AlphaMomentSplit
public import KsIndexLean.AlphaTransposeSquared

@[expose] public section


/-! Exact opposite-half and moment decomposition of the actual trial residual. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ AlphaResidual OppositeHalf

lemma tsum_chat_convS_trial_re (n : ℤ) :
    (∑' m : ℤ, chat (m-n) * (convS trial m).re) = (trial n).re := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum, trial_eq_real]
  have h := tsum_chat_convS_trial n
  convert h using 1
  apply tsum_congr
  intro m
  rw [Complex.ofReal_mul, convS_trial_eq_real]

/-- Opposite-sign frequency contribution to the transpose sum. -/
def oppositeResidualSum (n : ℤ) : ℝ :=
  ∑' m : ℤ, if (6*n+1)*(6*m+4) < 0 then
    sigM m * chat (m-n) * (convS trial m).re else 0

/-- The signed inverse-frequency moment of the actual trial convolution. -/
def signedTrialMoment : ℝ :=
  ∑' m : ℤ, (-1 : ℝ)^m * (convS trial m).re / (6*(m:ℝ)+4)

/-- The all-integer-index residual identity, including exact signed-moment cancellation. -/
theorem realResidual_split (s : ℝ) (n : ℤ) :
    realResidual s n =
      (1+s^2) * sigP n * (trial n).re + 2*s^2 * oppositeResidualSum n +
      (24*s^2 / (Real.pi * |6*(n:ℝ)+1|)) * (-1 : ℝ)^n * signedTrialMoment := by
  have h := OppositeHalf.tsum_split summable_abs_convS_trial_re n
  rw [tsum_chat_convS_trial_re, tsum_signed_convS_trial_re] at h
  rw [realResidual, h]
  dsimp [oppositeResidualSum, signedTrialMoment]
  ring

end KsIndex.AlphaRemarkTrial
