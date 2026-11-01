module

public import KsIndexLean.AlphaTrialGroups
public import KsIndexLean.PowerArcSignedTails

@[expose] public section


/-! Finite endpoint formula for the reflected signed convolution mass. -/
noncomputable section
namespace KsIndex.OppositeHalf
open CircleQ PowerArc KsIndex.AlphaRemarkTrial

def reflectedMass : ℝ :=
  (∑ t ∈ Finset.range 4, reflectedDemod t) +
    ∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
      (((9-shift i)+exponent i) * g (exponent i) (9-shift i) / (2*exponent i))

theorem reflectedDemod_tsum_eq : (∑' t : ℕ, reflectedDemod t) = reflectedMass := by
  have hs (i : Fin 25) : Summable (fun k : ℕ => (-1 : ℝ)^k *
      g (exponent i) ((9-shift i)+2*k)) := by
    apply Summable.of_abs
    simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
      abs_g_summable (exponent_pos i) (exponent_le_baseterm i)
  have he : (fun k : ℕ => reflectedDemod (k+4)) =
      fun k : ℕ => ∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
        ((-1 : ℝ)^k * g (exponent i) ((9-shift i)+2*k)) := by
    funext k
    rw [reflectedDemod_eq_sum, pow_add]
    norm_num only [show (-1 : ℝ)^4 = 1 by norm_num, mul_one]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    rw [show (2*((k : ℝ)+4)+1)-shift i = (9-shift i)+2*k by ring]
    ring
  have htail : (∑' k : ℕ, reflectedDemod (k+4)) =
      ∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
        (((9-shift i)+exponent i)*g (exponent i) (9-shift i)/(2*exponent i)) := by
    rw [he, Summable.tsum_finsetSum (fun i _ => (hs i).mul_left _)]
    apply Finset.sum_congr rfl
    intro i _
    rw [tsum_mul_left, signed_g_tsum (exponent_pos i)
      (by fin_cases i <;> norm_num [shift]) (exponent_le_baseterm i)]
  have hsplit := summable_reflectedDemod.sum_add_tsum_nat_add 4
  rw [htail] at hsplit
  exact hsplit.symm

end KsIndex.OppositeHalf
