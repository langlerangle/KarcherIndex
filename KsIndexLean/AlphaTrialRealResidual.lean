module

public import KsIndexLean.AlphaTrialPolynomialDecay

@[expose] public section


/-! The complex form residual equals the real coefficient expression for the fixed trial. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ PowerArc AlphaResidual

lemma coefficient_im_zero (i : Fin 25) : (coefficient i).im = 0 := by
  fin_cases i <;> norm_num [coefficient]

lemma trial_im_zero (n : ℤ) : (trial n).im = 0 := by
  simp [trial, powerTrial, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    normalizedPowerField_apply, Complex.mul_im, coefficient_im_zero]

lemma convS_trial_im_zero (m : ℤ) : (convS trial m).im = 0 := by
  rw [convS_trial]
  simp [Complex.mul_im, coefficient_im_zero]

lemma trial_eq_real (n : ℤ) : ((trial n).re : ℂ) = trial n := by
  apply Complex.ext <;> simp [trial_im_zero]

lemma convS_trial_eq_real (m : ℤ) : ((convS trial m).re : ℂ) = convS trial m := by
  apply Complex.ext <;> simp [convS_trial_im_zero]

lemma transpose_trial_eq_real (n : ℤ) :
    transposeCoefficient trial n =
      ((∑' m : ℤ, sigM m * chat (m-n) * (convS trial m).re) : ℝ) := by
  rw [transposeCoefficient, Complex.ofReal_tsum]
  apply tsum_congr
  intro m
  rw [← convS_trial_eq_real m]
  simp only [Complex.conj_ofReal, Complex.ofReal_re]
  push_cast
  ring

def realResidual (s : ℝ) (n : ℤ) : ℝ :=
  sigP n * (trial n).re + s^2 *
    (∑' m : ℤ, sigM m * chat (m-n) * (convS trial m).re)

/-- No conjugation or imaginary component remains in the actual trial residual. -/
theorem coefficientResidual_trial_eq (s : ℝ) (n : ℤ) :
    coefficientResidual s trial n = (realResidual s n : ℂ) := by
  rw [coefficientResidual, transpose_trial_eq_real, ← trial_eq_real n]
  simp only [Complex.conj_ofReal]
  simp only [realResidual, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow]

theorem coefficientResidual_trial_norm_sq (s : ℝ) (n : ℤ) :
    ‖coefficientResidual s trial n‖^2 = realResidual s n ^ 2 := by
  rw [coefficientResidual_trial_eq, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end KsIndex.AlphaRemarkTrial
