module

public import KsIndexLean.AlphaTrialSampleCertificate
public import KsIndexLean.IntegerWindowSum

@[expose] public section


/-! Exact decomposition into the coefficient window `[-8192,8192]` and four
infinite tails. The even and odd sample indices encode the two Fourier lattices. -/
namespace KsIndex.AlphaRemarkTrial.EnergyWindow8192
open CircleQ

noncomputable def finiteEnergy (s : ℝ) : ℝ :=
  (∑ n ∈ Finset.range 16385, sigP ((n:ℤ)-8192)*‖trial ((n:ℤ)-8192)‖^2) +
    s^2 * ∑ m ∈ Finset.range 16385,
      sigM ((m:ℤ)-8192)*‖convS trial ((m:ℤ)-8192)‖^2

lemma pplus_term (n : ℕ) :
    sigP ((n:ℤ)+8192+1)*‖trial ((n:ℤ)+8192+1)‖^2 =
      ((6*n+49159)-4/(6*n+49159))*sample (16386+2*n)^2 := by
  rw [trial_eq_sample]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hk : 2*((n:ℤ)+8192+1) = 16386+2*n := by ring
  rw [hk]
  congr 1
  unfold sigP
  push_cast
  rw [abs_of_pos (by positivity)]
  have h : (6*(n:ℝ)+49159) ≠ 0 := by positivity
  field_simp
  ring

lemma pminus_term (n : ℕ) :
    sigP (-((n:ℤ)+8192+1))*‖trial (-((n:ℤ)+8192+1))‖^2 =
      ((6*n+49157)-4/(6*n+49157))*sample (-16386-2*n)^2 := by
  rw [trial_eq_sample]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hk : 2*(-((n:ℤ)+8192+1)) = -16386-2*n := by ring
  rw [hk]
  congr 1
  unfold sigP
  push_cast
  rw [show 6*(-((n:ℝ)+8192+1))+1 = -(6*n+49157) by ring,
    abs_neg, abs_of_pos (by positivity)]
  have h : (6*(n:ℝ)+49157) ≠ 0 := by positivity
  field_simp

lemma mplus_term (n : ℕ) :
    sigM ((n:ℤ)+8192+1)*‖convS trial ((n:ℤ)+8192+1)‖^2 =
      ((6*n+49162)-4/(6*n+49162))*sample (16387+2*n)^2 := by
  rw [convS_eq_sample]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hk : 2*((n:ℤ)+8192+1)+1 = 16387+2*n := by ring
  rw [hk]
  congr 1
  unfold sigM
  push_cast
  rw [abs_of_pos (by positivity)]
  have h : (6*(n:ℝ)+49162) ≠ 0 := by positivity
  field_simp
  ring

lemma mminus_term (n : ℕ) :
    sigM (-((n:ℤ)+8192+1))*‖convS trial (-((n:ℤ)+8192+1))‖^2 =
      ((6*n+49154)-4/(6*n+49154))*sample (-16385-2*n)^2 := by
  rw [convS_eq_sample]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hk : 2*(-((n:ℤ)+8192+1))+1 = -16385-2*n := by ring
  rw [hk]
  congr 1
  unfold sigM
  push_cast
  rw [show 6*(-((n:ℝ)+8192+1))+4 = -(6*n+49154) by ring,
    abs_neg, abs_of_pos (by positivity)]
  have h : (6*(n:ℝ)+49154) ≠ 0 := by positivity
  field_simp

noncomputable def tails (s : ℝ) : ℝ :=
  (∑' n : ℕ, ((6*n+49159)-4/(6*n+49159))*sample (16386+2*n)^2) +
  (∑' n : ℕ, ((6*n+49157)-4/(6*n+49157))*sample (-16386-2*n)^2) +
  s^2 * ((∑' n : ℕ, ((6*n+49162)-4/(6*n+49162))*sample (16387+2*n)^2) +
    (∑' n : ℕ, ((6*n+49154)-4/(6*n+49154))*sample (-16385-2*n)^2))

/-- The energy cutoff is independent of the residual cutoff. -/
theorem qform_eq_finite_add_tails (s : ℝ) :
    Qform s trial = finiteEnergy s + tails s := by
  have hp := tsum_integer_window _ (summable_sigP_mul trial_memDom.1) 8192
  have hm := tsum_integer_window _ (summable_sigM_mul trial_memDom.2) 8192
  rw [Qform, hp, hm]
  simp only [Nat.cast_ofNat]
  simp_rw [pplus_term, pminus_term, mplus_term, mminus_term]
  unfold finiteEnergy tails
  ring

end KsIndex.AlphaRemarkTrial.EnergyWindow8192
