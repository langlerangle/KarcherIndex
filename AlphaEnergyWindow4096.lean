module

public import KsIndexLean.AlphaTrialSampleCertificate
public import KsIndexLean.IntegerWindowSum

@[expose] public section


/-! Exact decomposition into the coefficient window `[-4096,4096]` and four
infinite tails. The even and odd sample indices encode the two Fourier lattices. -/
namespace KsIndex.AlphaRemarkTrial.EnergyWindow4096
open CircleQ

noncomputable def finiteEnergy (s : ℝ) : ℝ :=
  (∑ n ∈ Finset.range 8193, sigP ((n:ℤ)-4096)*‖trial ((n:ℤ)-4096)‖^2) +
    s^2 * ∑ m ∈ Finset.range 8193,
      sigM ((m:ℤ)-4096)*‖convS trial ((m:ℤ)-4096)‖^2

lemma pplus_term (n : ℕ) :
    sigP ((n:ℤ)+4096+1)*‖trial ((n:ℤ)+4096+1)‖^2 =
      ((6*n+24583)-4/(6*n+24583))*sample (8194+2*n)^2 := by
  rw [trial_eq_sample]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hk : 2*((n:ℤ)+4096+1) = 8194+2*n := by ring
  rw [hk]
  congr 1
  unfold sigP
  push_cast
  rw [abs_of_pos (by positivity)]
  have h : (6*(n:ℝ)+24583) ≠ 0 := by positivity
  field_simp
  ring

lemma pminus_term (n : ℕ) :
    sigP (-((n:ℤ)+4096+1))*‖trial (-((n:ℤ)+4096+1))‖^2 =
      ((6*n+24581)-4/(6*n+24581))*sample (-8194-2*n)^2 := by
  rw [trial_eq_sample]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hk : 2*(-((n:ℤ)+4096+1)) = -8194-2*n := by ring
  rw [hk]
  congr 1
  unfold sigP
  push_cast
  rw [show 6*(-((n:ℝ)+4096+1))+1 = -(6*n+24581) by ring,
    abs_neg, abs_of_pos (by positivity)]
  have h : (6*(n:ℝ)+24581) ≠ 0 := by positivity
  field_simp

lemma mplus_term (n : ℕ) :
    sigM ((n:ℤ)+4096+1)*‖convS trial ((n:ℤ)+4096+1)‖^2 =
      ((6*n+24586)-4/(6*n+24586))*sample (8195+2*n)^2 := by
  rw [convS_eq_sample]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hk : 2*((n:ℤ)+4096+1)+1 = 8195+2*n := by ring
  rw [hk]
  congr 1
  unfold sigM
  push_cast
  rw [abs_of_pos (by positivity)]
  have h : (6*(n:ℝ)+24586) ≠ 0 := by positivity
  field_simp
  ring

lemma mminus_term (n : ℕ) :
    sigM (-((n:ℤ)+4096+1))*‖convS trial (-((n:ℤ)+4096+1))‖^2 =
      ((6*n+24578)-4/(6*n+24578))*sample (-8193-2*n)^2 := by
  rw [convS_eq_sample]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hk : 2*(-((n:ℤ)+4096+1))+1 = -8193-2*n := by ring
  rw [hk]
  congr 1
  unfold sigM
  push_cast
  rw [show 6*(-((n:ℝ)+4096+1))+4 = -(6*n+24578) by ring,
    abs_neg, abs_of_pos (by positivity)]
  have h : (6*(n:ℝ)+24578) ≠ 0 := by positivity
  field_simp

noncomputable def tails (s : ℝ) : ℝ :=
  (∑' n : ℕ, ((6*n+24583)-4/(6*n+24583))*sample (8194+2*n)^2) +
  (∑' n : ℕ, ((6*n+24581)-4/(6*n+24581))*sample (-8194-2*n)^2) +
  s^2 * ((∑' n : ℕ, ((6*n+24586)-4/(6*n+24586))*sample (8195+2*n)^2) +
    (∑' n : ℕ, ((6*n+24578)-4/(6*n+24578))*sample (-8193-2*n)^2))

/-- The energy cutoff is independent of the residual cutoff. -/
theorem qform_eq_finite_add_tails (s : ℝ) :
    Qform s trial = finiteEnergy s + tails s := by
  have hp := tsum_integer_window _ (summable_sigP_mul trial_memDom.1) 4096
  have hm := tsum_integer_window _ (summable_sigM_mul trial_memDom.2) 4096
  rw [Qform, hp, hm]
  simp only [Nat.cast_ofNat]
  simp_rw [pplus_term, pminus_term, mplus_term, mminus_term]
  unfold finiteEnergy tails
  ring

#print axioms qform_eq_finite_add_tails
end KsIndex.AlphaRemarkTrial.EnergyWindow4096
