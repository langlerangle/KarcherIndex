module

public import KsIndexLean.AlphaTrialInnerCertificate
public import KsIndexLean.AlphaTrialIntegerData

@[expose] public section


/-! Sample interval propagation for the actual finite corrected residual window. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ PowerArc CertifiedApproximation

/-- The finite transpose window evaluated at the certified sample centers. -/
def transposeWindowCenter (n : ℤ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T,
    (sigM t * chat ((t:ℤ)-n) * sampleCenter (2*(t:ℤ)+1) +
    sigM (-(t:ℤ)-1) * chat (-(t:ℤ)-1-n) * sampleCenter (-2*(t:ℤ)-1))

def transposeWindowRadius (n : ℤ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T,
    (|sigM t * chat ((t:ℤ)-n)| * sampleError (2*(t:ℤ)+1) +
    |sigM (-(t:ℤ)-1) * chat (-(t:ℤ)-1-n)| * sampleError (-2*(t:ℤ)-1))

lemma transposeTerm_sample_bound (n m : ℤ) :
    |transposeTerm n m - sigM m * chat (m-n) * sampleCenter (2*m+1)| ≤
      |sigM m * chat (m-n)| * sampleError (2*m+1) := by
  unfold transposeTerm
  rw [convS_eq_sample, Complex.ofReal_re, ← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (sample_bound _) (abs_nonneg _)

/-- Every term uses the same actual-trial sample certificate. -/
theorem transposeWindow_sample_bound (n : ℤ) (T : ℕ) :
    |(∑ t ∈ Finset.range T, pairedTransposeTerm n t) - transposeWindowCenter n T| ≤
      transposeWindowRadius n T := by
  unfold transposeWindowCenter transposeWindowRadius
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro t _
  have hp := transposeTerm_sample_bound n (t:ℤ)
  have hm := transposeTerm_sample_bound n (-(t:ℤ)-1)
  rw [show 2*(-(t:ℤ)-1)+1 = -2*(t:ℤ)-1 by ring] at hm
  have hh := (abs_add_le
    (transposeTerm n t - sigM t * chat ((t:ℤ)-n) * sampleCenter (2*(t:ℤ)+1))
    (transposeTerm n (-(t:ℤ)-1) - sigM (-(t:ℤ)-1) * chat (-(t:ℤ)-1-n) *
      sampleCenter (-2*(t:ℤ)-1))).trans (add_le_add hp hm)
  convert hh using 1
  unfold pairedTransposeTerm
  congr 1
  ring_nf

/-- The finite center with sample intervals propagated through the window.
The leading endpoint correction is retained exactly here. -/
def sampledResidualCenter (s : ℝ) (n : ℤ) (T : ℕ) : ℝ :=
  sigP n * sampleCenter (2*n) + s^2 * (transposeWindowCenter n T +
    (12/Real.pi) * (-1 : ℝ)^((T:ℤ)-n) * leadingTailB T)

def sampledResidualRadius (s : ℝ) (n : ℤ) (T : ℕ) : ℝ :=
  |sigP n| * sampleError (2*n) + s^2 * transposeWindowRadius n T

theorem correctedCenter_sample_bound (s : ℝ) (n : ℤ) (T : ℕ) :
    |correctedResidualCenter s n T - sampledResidualCenter s n T| ≤
      sampledResidualRadius s n T := by
  have hp := mul_le_mul_of_nonneg_left (sample_bound (2*n)) (abs_nonneg (sigP n))
  have hw := mul_le_mul_of_nonneg_left (transposeWindow_sample_bound n T) (sq_nonneg s)
  have hh := (abs_add_le
    (sigP n*(sample (2*n)-sampleCenter (2*n)))
    (s^2*((∑ t ∈ Finset.range T, pairedTransposeTerm n t)-transposeWindowCenter n T)))
  rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg s)] at hh
  have hb := hh.trans (add_le_add hp hw)
  unfold correctedResidualCenter sampledResidualCenter sampledResidualRadius
  rw [trial_eq_sample, Complex.ofReal_re]
  convert hb using 1
  congr 1
  ring_nf

/-- The remaining finite-value obligation is explicit, including all propagated
sample errors and the already certified infinite inner-tail error. -/
theorem realResidual_sampledWindow_bound (n : ℤ) (hcut : 4*(n:ℝ)^2 < 32771^2) :
    |realResidual AlphaRemark.spectralUpper n -
      sampledResidualCenter AlphaRemark.spectralUpper n 16385| ≤
      innerError16385 n + sampledResidualRadius AlphaRemark.spectralUpper n 16385 := by
  exact (abs_sub_le _ (correctedResidualCenter AlphaRemark.spectralUpper n 16385) _).trans
    (add_le_add (realResidual_inner_certificate n hcut)
      (correctedCenter_sample_bound AlphaRemark.spectralUpper n 16385))

end KsIndex.AlphaRemarkTrial
