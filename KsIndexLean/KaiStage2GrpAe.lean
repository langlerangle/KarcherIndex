module

public import KsIndexLean.AlphaRemainderIdentity
public import KsIndexLean.AlphaGroupDenomPositive

@[expose] public section


/-! Exact rational identification for the family-A, even-shift group.

The group uses odd arguments of `g`, so its normalized expression carries
the seed ratio `g β 1 / g β 0`, with `β = 2161809/5000000`.
The private lemmas express the required odd-frequency values as rational
multiples of `g β 1`. For real `n ≥ 3`, `bridge_grpAe` identifies the scaled
endpoint-mass, demodulated-group and correction expression with this seed
ratio times `GroupBounds.grpValue_0_0_p n`.
-/
noncomputable section
namespace KsIndex.Stage2GrpAe
open KsIndex.CircleQ KsIndex.PowerArc KsIndex.OppositeHalf KsIndex.AlphaRemarkTrial

set_option linter.style.longLine false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

private lemma fAe_m5 : g (2161809/5000000:ℝ) (-5) = g (2161809/5000000:ℝ) 1 * (12145746050827/155381926050827 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  have key : g (2161809/5000000:ℝ) ((-5:ℤ):ℝ) / g (2161809/5000000:ℝ) 0 = g (2161809/5000000:ℝ) 1 / g (2161809/5000000:ℝ) 0 * (12145746050827/155381926050827 : ℝ) := by
    rw [normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (-5:ℤ)]
    norm_num [integerSeedValue, normalizedCoefficient]
  rw [show ((-5:ℤ):ℝ) = (-5:ℝ) by norm_num] at key
  rw [div_mul_eq_mul_div, div_eq_div_iff h0 h0] at key
  exact mul_right_cancel₀ h0 key

private lemma fAe_m3 : g (2161809/5000000:ℝ) (-3) = g (2161809/5000000:ℝ) 1 * (-2838191/17161809 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  have key : g (2161809/5000000:ℝ) ((-3:ℤ):ℝ) / g (2161809/5000000:ℝ) 0 = g (2161809/5000000:ℝ) 1 / g (2161809/5000000:ℝ) 0 * (-2838191/17161809 : ℝ) := by
    rw [normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (-3:ℤ)]
    norm_num [integerSeedValue, normalizedCoefficient]
  rw [show ((-3:ℤ):ℝ) = (-3:ℝ) by norm_num] at key
  rw [div_mul_eq_mul_div, div_eq_div_iff h0 h0] at key
  exact mul_right_cancel₀ h0 key

private lemma fAe_m1 : g (2161809/5000000:ℝ) (-1) = g (2161809/5000000:ℝ) 1 * (1 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  have key : g (2161809/5000000:ℝ) ((-1:ℤ):ℝ) / g (2161809/5000000:ℝ) 0 = g (2161809/5000000:ℝ) 1 / g (2161809/5000000:ℝ) 0 * (1 : ℝ) := by
    rw [normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (-1:ℤ)]
    norm_num [integerSeedValue, normalizedCoefficient]
  rw [show ((-1:ℤ):ℝ) = (-1:ℝ) by norm_num] at key
  rw [div_mul_eq_mul_div, div_eq_div_iff h0 h0] at key
  exact mul_right_cancel₀ h0 key

private lemma fAe_3 : g (2161809/5000000:ℝ) (3) = g (2161809/5000000:ℝ) 1 * (-2838191/17161809 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  have key : g (2161809/5000000:ℝ) ((3:ℤ):ℝ) / g (2161809/5000000:ℝ) 0 = g (2161809/5000000:ℝ) 1 / g (2161809/5000000:ℝ) 0 * (-2838191/17161809 : ℝ) := by
    rw [normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (3:ℤ)]
    norm_num [integerSeedValue, normalizedCoefficient]
  rw [show ((3:ℤ):ℝ) = (3:ℝ) by norm_num] at key
  rw [div_mul_eq_mul_div, div_eq_div_iff h0 h0] at key
  exact mul_right_cancel₀ h0 key

private lemma fAe_5 : g (2161809/5000000:ℝ) (5) = g (2161809/5000000:ℝ) 1 * (12145746050827/155381926050827 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  have key : g (2161809/5000000:ℝ) ((5:ℤ):ℝ) / g (2161809/5000000:ℝ) 0 = g (2161809/5000000:ℝ) 1 / g (2161809/5000000:ℝ) 0 * (12145746050827/155381926050827 : ℝ) := by
    rw [normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (5:ℤ)]
    norm_num [integerSeedValue, normalizedCoefficient]
  rw [show ((5:ℤ):ℝ) = (5:ℝ) by norm_num] at key
  rw [div_mul_eq_mul_div, div_eq_div_iff h0 h0] at key
  exact mul_right_cancel₀ h0 key

private lemma fAe_7 : g (2161809/5000000:ℝ) (7) = g (2161809/5000000:ℝ) 1 * (-277386868146282733957/5774273457952957266043 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  have key : g (2161809/5000000:ℝ) ((7:ℤ):ℝ) / g (2161809/5000000:ℝ) 0 = g (2161809/5000000:ℝ) 1 / g (2161809/5000000:ℝ) 0 * (-277386868146282733957/5774273457952957266043 : ℝ) := by
    rw [normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (7:ℤ)]
    norm_num [integerSeedValue, normalizedCoefficient]
  rw [show ((7:ℤ):ℝ) = (7:ℝ) by norm_num] at key
  rw [div_mul_eq_mul_div, div_eq_div_iff h0 h0] at key
  exact mul_right_cancel₀ h0 key

private lemma fAe_9 : g (2161809/5000000:ℝ) (9) = g (2161809/5000000:ℝ) 1 * (9108882957079448357682151787/272325181937746901566282151787 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  have key : g (2161809/5000000:ℝ) ((9:ℤ):ℝ) / g (2161809/5000000:ℝ) 0 = g (2161809/5000000:ℝ) 1 / g (2161809/5000000:ℝ) 0 * (9108882957079448357682151787/272325181937746901566282151787 : ℝ) := by
    rw [normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (9:ℤ)]
    norm_num [integerSeedValue, normalizedCoefficient]
  rw [show ((9:ℤ):ℝ) = (9:ℝ) by norm_num] at key
  rw [div_mul_eq_mul_div, div_eq_div_iff h0 h0] at key
  exact mul_right_cancel₀ h0 key

private lemma fAe_11 : g (2161809/5000000:ℝ) (11) = g (2161809/5000000:ℝ) 1 * (-43356451990223801213447148393610813/1729622226201748697519291244506389187 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  have key : g (2161809/5000000:ℝ) ((11:ℤ):ℝ) / g (2161809/5000000:ℝ) 0 = g (2161809/5000000:ℝ) 1 / g (2161809/5000000:ℝ) 0 * (-43356451990223801213447148393610813/1729622226201748697519291244506389187 : ℝ) := by
    rw [normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (11:ℤ)]
    norm_num [integerSeedValue, normalizedCoefficient]
  rw [show ((11:ℤ):ℝ) = (11:ℝ) by norm_num] at key
  rw [div_mul_eq_mul_div, div_eq_div_iff h0 h0] at key
  exact mul_right_cancel₀ h0 key

private lemma fAe_13 : g (2161809/5000000:ℝ) (13) = g (2161809/5000000:ℝ) 1 * (29751642744698381055352625912038328791679/1508630618159956382971291069855979348791679 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  have key : g (2161809/5000000:ℝ) ((13:ℤ):ℝ) / g (2161809/5000000:ℝ) 0 = g (2161809/5000000:ℝ) 1 / g (2161809/5000000:ℝ) 0 * (29751642744698381055352625912038328791679/1508630618159956382971291069855979348791679 : ℝ) := by
    rw [normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (13:ℤ)]
    norm_num [integerSeedValue, normalizedCoefficient]
  rw [show ((13:ℤ):ℝ) = (13:ℝ) by norm_num] at key
  rw [div_mul_eq_mul_div, div_eq_div_iff h0 h0] at key
  exact mul_right_cancel₀ h0 key

private lemma fAe_15 : g (2161809/5000000:ℝ) (15) = g (2161809/5000000:ℝ) 1 * (-143810723796547777395925375339401054148640324053/8954512893077729682397047231971748924569839675947 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  have key : g (2161809/5000000:ℝ) ((15:ℤ):ℝ) / g (2161809/5000000:ℝ) 0 = g (2161809/5000000:ℝ) 1 / g (2161809/5000000:ℝ) 0 * (-143810723796547777395925375339401054148640324053/8954512893077729682397047231971748924569839675947 : ℝ) := by
    rw [normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (15:ℤ)]
    norm_num [integerSeedValue, normalizedCoefficient]
  rw [show ((15:ℤ):ℝ) = (15:ℝ) by norm_num] at key
  rw [div_mul_eq_mul_div, div_eq_div_iff h0 h0] at key
  exact mul_right_cancel₀ h0 key

/-- For real `n ≥ 3`, the family-A even-shift expression equals the odd seed
ratio times its rational group value. The proof supplies the required
nonzero denominators and reduces the identity to rational algebra. -/
theorem bridge_grpAe (n : ℝ) (hn : 3 ≤ n) :
    n * (6*(∑ i ∈ grpAe, endpointMass i) + 2*demodGroup grpAe n
        - (6*n+1-4/(6*n+1))*groupCorrectionRat grpAe (4323618/10000000) 15 (n+9/2))
      = (g (2161809/5000000:ℝ) 1 / g (2161809/5000000:ℝ) 0) * GroupBounds.grpValue_0_0_p n := by
  have hden := GroupBounds.grpDen_0_0_p_ne_zero n hn
  have hg0 : g (2161809/5000000:ℝ) 0 ≠ 0 :=
    (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  have z0 : (n+9/2:ℝ) ≠ 0 := by positivity
  have z1 : (n+9/2+1:ℝ) ≠ 0 := by positivity
  have z2 : (n+9/2+2:ℝ) ≠ 0 := by positivity
  have z3 : (n+9/2+3:ℝ) ≠ 0 := by positivity
  have z4 : (n+9/2+4:ℝ) ≠ 0 := by positivity
  have z5 : (n+9/2+5:ℝ) ≠ 0 := by positivity
  have h6 : (6*n+1:ℝ) ≠ 0 := by positivity
  have p1 : (2*n+1:ℝ) ≠ 0 := by positivity
  have p3 : (2*n+3:ℝ) ≠ 0 := by positivity
  have p5 : (2*n+5:ℝ) ≠ 0 := by positivity
  have p7 : (2*n+7:ℝ) ≠ 0 := by positivity
  have hg1 : g (2161809/5000000:ℝ) 1 ≠ 0 :=
    (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) zero_le_one le_rfl).ne'
  have hb0 : ((n * 2 + 9 + 2) * 10000000 - 2 * 72838191 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < (n * 2 + 9 + 2) * 10000000 - 2 * 72838191).ne'
  have hb1 : (10000000 * (n * 2 + 9 + 2 + 2) - 2 * 72838191 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < 10000000 * (n * 2 + 9 + 2 + 2) - 2 * 72838191).ne'
  have hb2 : (10000000 * (n * 2 + 9 + 2 ^ 2 + 2) - 2 * 72838191 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < 10000000 * (n * 2 + 9 + 2 ^ 2 + 2) - 2 * 72838191).ne'
  have hb3 : (10000000 * (n * 2 + 9 + 2 * 3 + 2) - 2 * 72838191 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < 10000000 * (n * 2 + 9 + 2 * 3 + 2) - 2 * 72838191).ne'
  have hb4 : (10000000 * (n * 2 + 9 + 2 * 4 + 2) - 2 * 72838191 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < 10000000 * (n * 2 + 9 + 2 * 4 + 2) - 2 * 72838191).ne'
  have hb5 : ((n * 2 + 9 + 2 * 5 + 2) * 10000000 - 2 * 72838191 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < (n * 2 + 9 + 2 * 5 + 2) * 10000000 - 2 * 72838191).ne'
  unfold GroupBounds.grpValue_0_0_p
  rw [← mul_div_assoc, eq_div_iff hden]
  unfold demodGroup groupCorrectionRat rationalGroupRest rationalCorrectionUnit trialGroupMult
  simp [grpAe, Finset.sum_filter, Fin.sum_univ_succ, Finset.sum_range_succ, endpointMass,
    coefficient, exponent, shift, chainLen, baseShift, zChainForceUnit, zChainCoeff,
    GroupBounds.grpNum_0_0_p, GroupBounds.grpDen_0_0_p]
  norm_num only
  simp only [fAe_m5, fAe_m3, fAe_m1, fAe_3, fAe_5, fAe_7, fAe_9, fAe_11, fAe_13, fAe_15]
  norm_num [normalizedCoefficient]
  field_simp
  ring

end KsIndex.Stage2GrpAe

#print axioms KsIndex.Stage2GrpAe.bridge_grpAe
