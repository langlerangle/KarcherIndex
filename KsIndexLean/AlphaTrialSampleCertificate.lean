module

public import KsIndexLean.AlphaRemarkTrial
public import KsIndexLean.PowerArcIntegerSamples
public import KsIndexLean.AlphaSeedApproximation

@[expose] public section


/-! Samplewise numerical error certificate for the concrete power-arc trial. -/

namespace KsIndex.AlphaRemarkTrial
open PowerArc

def numerator (i : Fin 25) : ℤ := if i.val < 12 then 2161809 else 2838191
noncomputable def seedCenter (i : Fin 25) : ℝ :=
  if i.val < 12 then 719689657/1000000000 else 738631771/1000000000
noncomputable def seedError (i : Fin 25) : ℝ :=
  if i.val < 12 then 3/1000000000 else 2/1000000000

lemma numerator_pos (i : Fin 25) : 0 < numerator i := by
  unfold numerator
  split_ifs <;> norm_num

lemma exponent_eq (i : Fin 25) : exponent i = (numerator i : ℝ) / 5000000 := by
  fin_cases i <;> norm_num [exponent, numerator]

lemma seed_error (i : Fin 25) :
    |g ((numerator i : ℝ) / 5000000) 1 / g ((numerator i : ℝ) / 5000000) 0 -
      seedCenter i| ≤ seedError i := by
  unfold numerator seedCenter seedError
  split_ifs
  · exact gamma_seed_approximation
  · exact beta_seed_approximation

lemma coefficient_real (i : Fin 25) : ((coefficient i).re : ℂ) = coefficient i := by
  fin_cases i <;> norm_num [coefficient]

noncomputable def sample (k : ℤ) : ℝ :=
  ∑ i : Fin 25, (coefficient i).re * (g (exponent i) (k + shift i) / g (exponent i) 0)

noncomputable def sampleCenter (k : ℤ) : ℝ :=
  ∑ i : Fin 25, (coefficient i).re *
    integerSampleCenter (numerator i) 5000000 (10^30) (seedCenter i) (k + shift i)

noncomputable def sampleError (k : ℤ) : ℝ :=
  ∑ i : Fin 25, |(coefficient i).re| *
    integerSampleError (numerator i) 5000000 (10^30) (seedCenter i) (seedError i) (k + shift i)

theorem sample_bound (k : ℤ) : |sample k - sampleCenter k| ≤ sampleError k := by
  apply CertifiedApproximation.finite_linear_error
  intro i _
  have hh := integerSample_bound (numerator_pos i) (by norm_num : (0 : ℤ) < 5000000)
    (by norm_num : (0 : ℤ) < 10^30) (seed_error i) (k + shift i)
  simpa only [exponent_eq, Int.cast_add, Int.cast_ofNat] using hh

theorem trial_eq_sample (n : ℤ) : trial n = (sample (2 * n) : ℂ) := by
  simp only [trial, powerTrial, sample, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, normalizedPowerField_apply]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [coefficient_real]

theorem convS_eq_sample (m : ℤ) : CircleQ.convS trial m = (sample (2 * m + 1) : ℂ) := by
  rw [convS_trial]
  simp only [sample]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [coefficient_real]
  rw [show (2 : ℝ) * m + ((shift i : ℝ) + 1) = 2 * m + 1 + shift i by ring]

theorem sampleError_nonneg (k : ℤ) : 0 ≤ sampleError k :=
  (abs_nonneg _).trans (sample_bound k)

theorem finite_trial_energy_error (p q : Finset ℤ) (s : ℝ) :
    |((∑ n ∈ p, CircleQ.sigP n * ‖trial n‖ ^ 2) +
      s ^ 2 * ∑ m ∈ q, CircleQ.sigM m * ‖CircleQ.convS trial m‖ ^ 2) -
      ((∑ n ∈ p, CircleQ.sigP n * sampleCenter (2 * n) ^ 2) +
      s ^ 2 * ∑ m ∈ q, CircleQ.sigM m * sampleCenter (2 * m + 1) ^ 2)| ≤
      (∑ n ∈ p, |CircleQ.sigP n| *
        (sampleError (2 * n) * (2 * |sampleCenter (2 * n)| + sampleError (2 * n)))) +
      s ^ 2 * ∑ m ∈ q, |CircleQ.sigM m| *
        (sampleError (2 * m + 1) * (2 * |sampleCenter (2 * m + 1)| +
          sampleError (2 * m + 1))) := by
  have hp := CertifiedApproximation.finite_quadratic_error p CircleQ.sigP
    (fun n => sample (2 * n)) (fun n => sampleCenter (2 * n))
    (fun n => sampleError (2 * n))
    (fun n _ => sampleError_nonneg _) (fun n _ => sample_bound _)
  have hq := CertifiedApproximation.finite_quadratic_error q CircleQ.sigM
    (fun m => sample (2 * m + 1)) (fun m => sampleCenter (2 * m + 1))
    (fun m => sampleError (2 * m + 1))
    (fun m _ => sampleError_nonneg _) (fun m _ => sample_bound _)
  simp only [trial_eq_sample, convS_eq_sample, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h := abs_add_le
    ((∑ n ∈ p, CircleQ.sigP n * sample (2 * n) ^ 2) -
      ∑ n ∈ p, CircleQ.sigP n * sampleCenter (2 * n) ^ 2)
    (s ^ 2 * ((∑ m ∈ q, CircleQ.sigM m * sample (2 * m + 1) ^ 2) -
      ∑ m ∈ q, CircleQ.sigM m * sampleCenter (2 * m + 1) ^ 2))
  rw [abs_mul, abs_of_nonneg (sq_nonneg s)] at h
  have hb := add_le_add hp (mul_le_mul_of_nonneg_left hq (sq_nonneg s))
  convert h.trans hb using 1
  · congr 1 <;> ring

end KsIndex.AlphaRemarkTrial
