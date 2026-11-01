module

public import KsIndexLean.AlphaRemainderIdentity
public import KsIndexLean.AlphaGroupDenomPositive

@[expose] public section


/-! Reflected rational identification for the family-B, odd-shift group.

For real `n ≥ 3`, `bridge_grpBo_neg` identifies the expression using
`endpointMassPos`, `demodGroupPos` and `groupCorrectionRatR`, with the
factor `6*n-1-4/(6*n-1)`, as `GroupBounds.grpValue_1_1_m n` after scaling
by `n`. At `β = 2838191/5000000`, the even-frequency values of `g β`
normalize to rational multiples of `g β 0`, leaving no seed ratio.
The proof establishes the nonzero denominators and applies these exact
coefficient identities before rational simplification.
-/
noncomputable section
namespace KsIndex.Stage2GrpBoNeg
open KsIndex.CircleQ KsIndex.PowerArc KsIndex.OppositeHalf KsIndex.AlphaRemarkTrial

set_option linter.style.longLine false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

private lemma fBo_A1_m4 : g (2838191/5000000:ℝ) (-4) / g (2838191/5000000:ℝ) 0 = (-20326581847519/293201058152481 : ℝ) := by
  rw [show ((-4:ℝ)) = ((-4:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2838191/5000000) (-4:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fBo_B_m4 : g (2838191/5000000:ℝ) (-4) = g (2838191/5000000:ℝ) 0 * (-20326581847519/293201058152481 : ℝ) := by
  have h0 : g (2838191/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2838191/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fBo_A1_m4

private lemma fBo_A1_m2 : g (2838191/5000000:ℝ) (-2) / g (2838191/5000000:ℝ) 0 = (2838191/12838191 : ℝ) := by
  rw [show ((-2:ℝ)) = ((-2:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2838191/5000000) (-2:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fBo_B_m2 : g (2838191/5000000:ℝ) (-2) = g (2838191/5000000:ℝ) 0 * (2838191/12838191 : ℝ) := by
  have h0 : g (2838191/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2838191/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fBo_A1_m2

private lemma fBo_A1_0 : g (2838191/5000000:ℝ) 0 / g (2838191/5000000:ℝ) 0 = (1:ℝ) := div_self (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2838191/5000000) le_rfl zero_le_one).ne'

private lemma fBo_A1_2 : g (2838191/5000000:ℝ) (2) / g (2838191/5000000:ℝ) 0 = (2838191/12838191 : ℝ) := by
  rw [show ((2:ℝ)) = ((2:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2838191/5000000) (2:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fBo_B_2 : g (2838191/5000000:ℝ) (2) = g (2838191/5000000:ℝ) 0 * (2838191/12838191 : ℝ) := by
  have h0 : g (2838191/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2838191/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fBo_A1_2

private lemma fBo_A1_4 : g (2838191/5000000:ℝ) (4) / g (2838191/5000000:ℝ) 0 = (-20326581847519/293201058152481 : ℝ) := by
  rw [show ((4:ℝ)) = ((4:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2838191/5000000) (4:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fBo_B_4 : g (2838191/5000000:ℝ) (4) = g (2838191/5000000:ℝ) 0 * (-20326581847519/293201058152481 : ℝ) := by
  have h0 : g (2838191/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2838191/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fBo_A1_4

private lemma fBo_A1_6 : g (2838191/5000000:ℝ) (6) / g (2838191/5000000:ℝ) 0 = (116280305096662733957/3209397449671092733957 : ℝ) := by
  rw [show ((6:ℝ)) = ((6:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2838191/5000000) (6:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fBo_B_6 : g (2838191/5000000:ℝ) (6) = g (2838191/5000000:ℝ) 0 * (116280305096662733957/3209397449671092733957 : ℝ) := by
  have h0 : g (2838191/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2838191/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fBo_A1_6

private lemma fBo_A1_8 : g (2838191/5000000:ℝ) (8) / g (2838191/5000000:ℝ) 0 = (-3158383437497279717157848213/137484780943923157715962151787 : ℝ) := by
  rw [show ((8:ℝ)) = ((8:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2838191/5000000) (8:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fBo_B_8 : g (2838191/5000000:ℝ) (8) = g (2838191/5000000:ℝ) 0 * (-3158383437497279717157848213/137484780943923157715962151787 : ℝ) := by
  have h0 : g (2838191/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2838191/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fBo_A1_8

private lemma fBo_A1_10 : g (2838191/5000000:ℝ) (10) / g (2838191/5000000:ℝ) 0 = (16767320293291049552656282591785331/1037778159301167442388447417841785331 : ℝ) := by
  rw [show ((10:ℝ)) = ((10:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2838191/5000000) (10:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fBo_B_10 : g (2838191/5000000:ℝ) (10) = g (2838191/5000000:ℝ) 0 * (16767320293291049552656282591785331/1037778159301167442388447417841785331 : ℝ) := by
  have h0 : g (2838191/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2838191/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fBo_A1_10

private lemma fBo_A1_12 : g (2838191/5000000:ℝ) (12) / g (2838191/5000000:ℝ) 0 = (-87864128568224051156879004693756083291531/7245789132199465140865195003977657156708469 : ℝ) := by
  rw [show ((12:ℝ)) = ((12:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2838191/5000000) (12:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fBo_B_12 : g (2838191/5000000:ℝ) (12) = g (2838191/5000000:ℝ) 0 * (-87864128568224051156879004693756083291531/7245789132199465140865195003977657156708469 : ℝ) := by
  have h0 : g (2838191/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2838191/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fBo_A1_12

private lemma fBo_A1_14 : g (2838191/5000000:ℝ) (14) / g (2838191/5000000:ℝ) 0 = (5022472535168266681435746702414588725698586339579/527770172756868892028180978951970351712848396339579 : ℝ) := by
  rw [show ((14:ℝ)) = ((14:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2838191/5000000) (14:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fBo_B_14 : g (2838191/5000000:ℝ) (14) = g (2838191/5000000:ℝ) 0 * (5022472535168266681435746702414588725698586339579/527770172756868892028180978951970351712848396339579 : ℝ) := by
  have h0 : g (2838191/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2838191/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fBo_A1_14

theorem bridge_grpBo_neg (n : ℝ) (hn : 3 ≤ n) :
    n * (6*(∑ i ∈ grpBo, endpointMassPos i) + 2*demodGroupPos grpBo n
        - (6*n-1-4/(6*n-1))*groupCorrectionRatR grpBo (5676382/10000000) 14 (n+9/2))
      = GroupBounds.grpValue_1_1_m n := by
  have hden := GroupBounds.grpDen_1_1_m_ne_zero n hn
  have hg0 : g (2838191/5000000:ℝ) 0 ≠ 0 :=
    (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2838191/5000000) le_rfl zero_le_one).ne'
  have z0 : (n+9/2:ℝ) ≠ 0 := by positivity
  have z1 : (n+9/2+1:ℝ) ≠ 0 := by positivity
  have z2 : (n+9/2+2:ℝ) ≠ 0 := by positivity
  have z3 : (n+9/2+3:ℝ) ≠ 0 := by positivity
  have z4 : (n+9/2+4:ℝ) ≠ 0 := by positivity
  have h6 : (n*6-1:ℝ) ≠ 0 := (by nlinarith [hn] : (0:ℝ) < n*6-1).ne'
  have p1 : (2*n+1:ℝ) ≠ 0 := by positivity
  have p3 : (2*n+3:ℝ) ≠ 0 := by positivity
  have p5 : (2*n+5:ℝ) ≠ 0 := by positivity
  have p7 : (2*n+7:ℝ) ≠ 0 := by positivity
  have hb0 : (10000000 * (n * 2 + 9 + 2) - 2 * 67161809 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < 10000000 * (n * 2 + 9 + 2) - 2 * 67161809).ne'
  have hb1 : (10000000 * (n * 2 + 9 + 2 + 2) - 2 * 67161809 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < 10000000 * (n * 2 + 9 + 2 + 2) - 2 * 67161809).ne'
  have hb2 : (10000000 * (n * 2 + 9 + 2 ^ 2 + 2) - 2 * 67161809 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < 10000000 * (n * 2 + 9 + 2 ^ 2 + 2) - 2 * 67161809).ne'
  have hb3 : (10000000 * (n * 2 + 9 + 2 * 3 + 2) - 2 * 67161809 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < 10000000 * (n * 2 + 9 + 2 * 3 + 2) - 2 * 67161809).ne'
  have hb4 : (10000000 * (n * 2 + 9 + 2 * 4 + 2) - 2 * 67161809 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < 10000000 * (n * 2 + 9 + 2 * 4 + 2) - 2 * 67161809).ne'
  unfold GroupBounds.grpValue_1_1_m
  rw [eq_div_iff hden]
  unfold demodGroupPos groupCorrectionRatR rationalGroupRest rationalCorrectionUnit trialGroupMultR
  simp [grpBo, Finset.sum_filter, Fin.sum_univ_succ, Finset.sum_range_succ, endpointMassPos,
    coefficient, exponent, shift, chainLenR, baseShift, zChainForceUnit, zChainCoeff,
    GroupBounds.grpNum_1_1_m, GroupBounds.grpDen_1_1_m]
  norm_num only
  simp only [fBo_B_m4, fBo_B_m2, fBo_B_2, fBo_B_4, fBo_B_6, fBo_B_8, fBo_B_10, fBo_B_12, fBo_B_14, fBo_A1_0]
  norm_num [normalizedCoefficient]
  field_simp
  ring

end KsIndex.Stage2GrpBoNeg

#print axioms KsIndex.Stage2GrpBoNeg.bridge_grpBo_neg
