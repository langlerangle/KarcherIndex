module

public import KsIndexLean.AlphaTrialWindowSamples
public import KsIndexLean.IntegerLinearCertificate

@[expose] public section


/-! Exact integer linear-sum certificates for the direct low-mode convolution. -/
namespace KsIndex.AlphaRemarkTrial
open CircleQ CertifiedApproximation

/-- The rational convolution weight with the common factor 2/pi removed. -/
def rationalKernelWeight (n m : ℤ) : ℚ :=
  (((6*(m : ℚ)+4)^2-4)/|6*(m : ℚ)+4|) * (-1 : ℚ)^(m-n) /
    (2*((m : ℚ)-n)+1)

theorem rationalKernelWeight_cast (n m : ℤ) :
    sigM m * chat (m-n) = (2/Real.pi) * (rationalKernelWeight n m : ℝ) := by
  simp [rationalKernelWeight, sigM, chat]
  ring

/-- Integer numerator of the rounded linear accumulation at scale 10^51. -/
def lowLinearNumerator (p : Finset ℤ) (n : ℤ) : ℤ :=
  ∑ m ∈ p, (rationalKernelWeight n m).num * sampleNumerator (2*m+1) /
    ((rationalKernelWeight n m).den : ℤ)

/-- Propagated sample errors plus both integer-rounding units. -/
def lowLinearRadius (p : Finset ℤ) (n : ℤ) : ℤ :=
  ∑ m ∈ p, (|(rationalKernelWeight n m).num| * sampleRadius (2*m+1) /
    ((rationalKernelWeight n m).den : ℤ) + 2)

/-- The actual sample convolution is enclosed by the integer accumulation.
This theorem requires no computed sample centers as hypotheses. -/
theorem lowLinear_bound (p : Finset ℤ) (n : ℤ) :
    |(∑ m ∈ p, (rationalKernelWeight n m : ℝ)*sample (2*m+1)) -
      (lowLinearNumerator p n : ℝ)/10^51| ≤ (lowLinearRadius p n : ℝ)/10^51 := by
  have h := finite_integer_linear_error p (fun m => sample (2*m+1))
    (fun m => (rationalKernelWeight n m).num)
    (fun m => ((rationalKernelWeight n m).den : ℤ))
    (fun m => sampleNumerator (2*m+1)) (fun m => sampleRadius (2*m+1))
    (by norm_num : (0 : ℤ) < 10^51)
    (by intro m _; exact_mod_cast (rationalKernelWeight n m).den_pos)
    (by intro m _; simpa only [Int.cast_pow, Int.cast_ofNat] using integer_sample_certificate (2*m+1))
  simpa only [Int.cast_natCast, Int.cast_pow, Int.cast_ofNat, ← Rat.cast_def,
    lowLinearNumerator, lowLinearRadius] using h

/-- Restore the common analytic factor after the signed integer accumulation. -/
theorem transpose_finite_integer_bound (p : Finset ℤ) (n : ℤ) :
    |(∑ m ∈ p, transposeTerm n m) -
      (2/Real.pi)*((lowLinearNumerator p n : ℝ)/10^51)| ≤
      (2/Real.pi)*((lowLinearRadius p n : ℝ)/10^51) := by
  have he : (∑ m ∈ p, transposeTerm n m) =
      (2/Real.pi)*(∑ m ∈ p, (rationalKernelWeight n m : ℝ)*sample (2*m+1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    unfold transposeTerm
    rw [convS_eq_sample, Complex.ofReal_re, rationalKernelWeight_cast]
    ring
  rw [he, ← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2/Real.pi)]
  exact mul_le_mul_of_nonneg_left (lowLinear_bound p n) (by positivity)

/-- Pairing nonnegative and negative indices gives exactly the direct window. -/
theorem sum_paired_integer_window (f : ℤ → ℝ) (T : ℕ) :
    (∑ t ∈ Finset.range T, (f (t : ℤ) + f (-(t : ℤ)-1))) =
      ∑ m ∈ Finset.Ico (-(T : ℤ)) (T : ℤ), f m := by
  induction T with
  | zero => simp
  | succ T ih =>
    have he : Finset.Ico (-((T+1 : ℕ) : ℤ)) ((T+1 : ℕ) : ℤ) =
        insert (-((T : ℤ)+1)) (insert (T : ℤ) (Finset.Ico (-(T : ℤ)) (T : ℤ))) := by
      ext m
      simp only [Finset.mem_Ico, Finset.mem_insert, Nat.cast_add, Nat.cast_one]
      omega
    rw [Finset.sum_range_succ, ih, he]
    have hp : (T : ℤ) ∉ Finset.Ico (-(T : ℤ)) (T : ℤ) := by simp
    have hm : -((T : ℤ)+1) ∉ insert (T : ℤ) (Finset.Ico (-(T : ℤ)) (T : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [Finset.sum_insert hm, Finset.sum_insert hp]
    rw [show -(T : ℤ)-1 = -((T : ℤ)+1) by ring]
    ring

/-- The integer certificate has the same paired convention as the analytic tail theorem. -/
theorem pairedTranspose_integer_bound (n : ℤ) (T : ℕ) :
    |(∑ t ∈ Finset.range T, pairedTransposeTerm n t) -
      (2/Real.pi)*((lowLinearNumerator (Finset.Ico (-(T : ℤ)) T) n : ℝ)/10^51)| ≤
      (2/Real.pi)*((lowLinearRadius (Finset.Ico (-(T : ℤ)) T) n : ℝ)/10^51) := by
  have he : (∑ t ∈ Finset.range T, pairedTransposeTerm n t) =
      ∑ m ∈ Finset.Ico (-(T : ℤ)) T, transposeTerm n m := by
    simpa only [pairedTransposeTerm] using sum_paired_integer_window (transposeTerm n) T
  rw [he]
  exact transpose_finite_integer_bound _ n

end KsIndex.AlphaRemarkTrial
