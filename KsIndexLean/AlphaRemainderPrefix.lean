module

public import KsIndexLean.AlphaTrialCompensatedNegative
public import KsIndexLean.AlphaTrialCompensatedResidual

@[expose] public section


/-! Finite-prefix cancellation in the rational residual remainder. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial

/-- Partial fractions with the common affine denominator relation retained. -/
lemma remainder_prefix_fraction (L X Y : ℝ) (hL : L ≠ 0) (hX : X ≠ 0)
    (hY : Y ≠ 0) (h : L + X = 3*Y) :
    (X-4/X)/Y = 3-(L-4/L)/Y-12/(L*X) := by
  field_simp
  linear_combination (L*X-4)*h

/-- The mass and two prefix transforms combine into the weighted finite prefix.
The parameter δ is 1 for the positive side and -1 for the negative side. -/
theorem remainder_prefix_sum (v : ℕ → ℝ) (N : ℕ) (n δ : ℝ)
    (hn : 1 ≤ n) (hδlo : -1 ≤ δ) (hδhi : δ ≤ 1) :
    6*(∑ t ∈ Finset.range N, v t) -
      (6*n+δ-4/(6*n+δ))*(∑ t ∈ Finset.range N, v t/((t : ℝ)+n+1/2)) -
      4/(6*n+δ)*(∑ t ∈ Finset.range N, v t/((t : ℝ)+(3-δ)/6)) =
      2*(∑ t ∈ Finset.range N,
        v t*((6*(t : ℝ)+3-δ)-4/(6*(t : ℝ)+3-δ))/(2*(t : ℝ)+2*n+1)) := by
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hL : 6*n+δ ≠ 0 := ne_of_gt (by linarith)
  have hX : 6*(t : ℝ)+3-δ ≠ 0 := ne_of_gt (by linarith)
  have hY : 2*(t : ℝ)+2*n+1 ≠ 0 := ne_of_gt (by linarith)
  have ha : (t : ℝ)+n+1/2 = (2*(t : ℝ)+2*n+1)/2 := by ring
  have hb : (t : ℝ)+(3-δ)/6 = (6*(t : ℝ)+3-δ)/6 := by ring
  rw [ha, hb]
  field_simp [hL, hX, hY]
  ring

open OppositeHalf

/-- The generator's finite-prefix form, with the actual moment retained. -/
theorem rawRemainder_eq_weighted_prefix (n : ℝ) (hn : 1 ≤ n) :
    rawRemainder n =
      6*(reflectedMass-∑ t ∈ Finset.range 4, reflectedDemod t) +
      2*(∑ t ∈ Finset.range 4,
        reflectedDemod t*((6*(t : ℝ)+2)-4/(6*(t : ℝ)+2))/(2*(t : ℝ)+2*n+1)) +
      (12*signedTrialMoment-4*reducedMomentLower (13/3))/(6*n+1) -
      (6*n+1-4/(6*n+1))*allGroupCorrections (n+9/2) := by
  have h := remainder_prefix_sum reflectedDemod 4 n 1 hn (by norm_num) (by norm_num)
  norm_num only at h
  rw [signedTrialMoment_eq_reduced]
  unfold rawRemainder reflectedMomentPrefix
  simp only [show ∀ t : ℕ, 6*(t : ℝ)+3-1 = 6*(t : ℝ)+2 by intro t; ring] at h
  simp only [add_assoc] at h ⊢
  linear_combination h

/-- The same cancellation for negative residual indices. -/
theorem rawRemainderNegative_eq_weighted_prefix (n : ℝ) (hn : 1 ≤ n) :
    rawRemainderNegative n =
      6*(positiveMass-∑ t ∈ Finset.range 4, positiveDemod t) +
      2*(∑ t ∈ Finset.range 4,
        positiveDemod t*((6*(t : ℝ)+4)-4/(6*(t : ℝ)+4))/(2*(t : ℝ)+2*n+1)) +
      (12*signedTrialMoment-4*reducedMomentUpper (14/3))/(6*n-1) -
      (6*n-1-4/(6*n-1))*allGroupCorrectionsR (n+9/2) := by
  have h := remainder_prefix_sum positiveDemod 4 n (-1) hn (by norm_num) (by norm_num)
  rw [signedTrialMoment_eq_reduced]
  unfold rawRemainderNegative positiveMomentPrefix
  norm_num only at h
  simp only [show ∀ t : ℕ, 6*(t : ℝ)+3-(-1) = 6*(t : ℝ)+4 by intro t; ring,
    add_assoc] at h ⊢
  linear_combination h

end KsIndex.AlphaRemarkTrial
