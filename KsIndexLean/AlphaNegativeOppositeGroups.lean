module

public import KsIndexLean.AlphaPositiveMoments

@[expose] public section


/-! Opposite-half decomposition at negative residual indices. -/
noncomputable section
namespace KsIndex.OppositeHalf
open CircleQ Real PowerArc KsIndex.AlphaRemarkTrial

lemma negative_opposite_pointwise (n : ℤ) (hn : 1 ≤ n) (t : ℕ) :
    sigM t * chat ((t : ℤ)+n) * vTrial t =
      2 / π * (-1 : ℝ)^n *
        (3 - sigP (-n)/(2*(t : ℝ)+2*n+1) -
          12/((6*(n : ℝ)-1)*(6*t+4))) * positiveDemod t := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hL : (0 : ℝ) < 6*(n : ℝ)-1 := by linarith
  have hX : (0 : ℝ) < 6*(t : ℝ)+4 := by positivity
  have hY : (0 : ℝ) < 2*(t : ℝ)+2*n+1 := by linarith
  simp only [sigM, sigP, chat, positiveDemod, Int.cast_natCast, Int.cast_add,
    Int.cast_neg, zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), zpow_natCast]
  rw [abs_of_pos hX, abs_of_neg (show 6*(-(n : ℝ))+1 < 0 by linarith)]
  rw [show -(6*(-(n : ℝ))+1) = 6*(n : ℝ)-1 by ring]
  field_simp
  ring

/-- For n>=1, the opposite half at -n is the nonnegative m-lattice. -/
theorem negative_opposite_group_decomposition (n : ℤ) (hn : 1 ≤ n) :
    oppositeResidualSum (-n) =
      2 / π * (-1 : ℝ)^n *
        (3 * (∑' t : ℕ, positiveDemod t)
         - sigP (-n) * (1/2) *
            ((∑ t ∈ Finset.range 4, positiveDemod t / ((t : ℝ)+((n : ℝ)+1/2)))
             + ∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
                 powerArcStieltjes (exponent i) (9+shift i) (((n : ℝ)+1/2)+4))
         - 12/(6*(n : ℝ)-1) * (1/6) *
            ((∑ t ∈ Finset.range 4, positiveDemod t / ((t : ℝ)+2/3))
             + ∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
                 powerArcStieltjes (exponent i) (9+shift i) ((2/3 : ℝ)+4))) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hz1 : (0 : ℝ)<(n : ℝ)+1/2 := by linarith
  have hz2 : (0 : ℝ)<2/3 := by norm_num
  have hinj : Function.Injective (fun t : ℕ => (t : ℤ)) := (fun a b h => by simp only at h; omega)
  have hsupp : Function.support (fun m : ℤ =>
      if (6*(-n)+1)*(6*m+4)<0 then sigM m*chat (m-(-n))*vTrial m else 0) ⊆
      Set.range (fun t : ℕ => (t : ℤ)) := by
    intro m hm
    by_cases h : 0 ≤ m
    · exact ⟨m.toNat, Int.toNat_of_nonneg h⟩
    · exfalso
      apply hm
      have h0 : ¬ (6*(-n)+1)*(6*m+4)<0 := by
        have ha : 6*(-n)+1 < 0 := by omega
        have hb : 6*m+4 < 0 := by omega
        exact not_lt.mpr (le_of_lt (mul_pos_of_neg_of_neg ha hb))
      simp only [ite_eq_right h0]
  change (∑' m : ℤ, if (6*(-n)+1)*(6*m+4)<0 then
    sigM m*chat (m-(-n))*vTrial m else 0) = _
  rw [← Function.Injective.tsum_eq hinj hsupp]
  have hstep : (∑' t : ℕ, if (6*(-n)+1)*(6*(t : ℤ)+4)<0 then
      sigM t*chat ((t : ℤ)-(-n))*vTrial t else 0) =
      (∑' t : ℕ,
        ((2 / π * (-1 : ℝ) ^ n * 3) * positiveDemod t
         + (-(2 / π * (-1 : ℝ) ^ n * sigP (-n) * (1/2))) *
             (positiveDemod t / ((t : ℝ) + ((n : ℝ) + 1/2)))
         + (-(2 / π * (-1 : ℝ) ^ n * (12 / (6 * (n : ℝ) - 1)) * (1/6))) *
             (positiveDemod t / ((t : ℝ) + 2/3)))) := by
    apply tsum_congr
    intro t
    rw [ite_eq_left (mul_neg_of_neg_of_pos (show 6*(-n)+1<0 by omega)
      (show (0 : ℤ)<6*(t : ℤ)+4 by omega)), sub_neg_eq_add,
      negative_opposite_pointwise n hn t,
      show 2*(t : ℝ)+2*n+1 = 2*((t : ℝ)+((n : ℝ)+1/2)) by ring,
      show 6*(t : ℝ)+4 = 6*((t : ℝ)+2/3) by ring]
    field_simp
    ring
  have s1 := summable_positiveDemod.mul_left (2 / π * (-1 : ℝ) ^ n * 3)
  have s2 := (summable_positiveDemod_div hz1).mul_left
    (-(2 / π * (-1 : ℝ) ^ n * sigP (-n) * (1/2)))
  have s3 := (summable_positiveDemod_div hz2).mul_left
    (-(2 / π * (-1 : ℝ) ^ n * (12 / (6 * (n : ℝ) - 1)) * (1/6)))
  have hsplit : (∑' t : ℕ,
        ((2 / π * (-1 : ℝ) ^ n * 3) * positiveDemod t
         + (-(2 / π * (-1 : ℝ) ^ n * sigP (-n) * (1/2))) *
             (positiveDemod t / ((t : ℝ) + ((n : ℝ) + 1/2)))
         + (-(2 / π * (-1 : ℝ) ^ n * (12 / (6 * (n : ℝ) - 1)) * (1/6))) *
             (positiveDemod t / ((t : ℝ) + 2/3)))) =
      2 / π * (-1 : ℝ) ^ n *
        (3 * (∑' t : ℕ, positiveDemod t)
         - sigP (-n) * (1/2) *
            ((∑ t ∈ Finset.range 4, positiveDemod t / ((t : ℝ) + ((n : ℝ) + 1/2)))
             + ∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
                 powerArcStieltjes (exponent i) (9 + shift i) (((n : ℝ) + 1/2) + 4))
         - 12 / (6 * (n : ℝ) - 1) * (1/6) *
            ((∑ t ∈ Finset.range 4, positiveDemod t / ((t : ℝ) + 2/3))
             + ∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
                 powerArcStieltjes (exponent i) (9 + shift i) ((2/3 : ℝ) + 4))) := by
    rw [(s1.add s2).tsum_add s3, s1.tsum_add s2, tsum_mul_left, tsum_mul_left,
      tsum_mul_left, positive_shifted_tsum ((n : ℝ) + 1/2) hz1,
      positive_shifted_tsum (2/3) hz2]
    ring
  exact hstep.trans hsplit


end KsIndex.OppositeHalf
