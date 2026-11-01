module

public import KsIndexLean.AlphaRemainderIdentity
public import KsIndexLean.AlphaGroupDenomPositive

@[expose] public section


/-! Reflected rational identification for the family-A, odd-shift group.

For real `n ≥ 3`, `bridge_grpAo_neg` identifies the expression using
`endpointMassPos`, `demodGroupPos` and `groupCorrectionRatR`, with the
factor `6*n-1-4/(6*n-1)`, as `GroupBounds.grpValue_0_1_m n` after scaling
by `n`. At `β = 2161809/5000000`, the even-frequency values of `g β`
normalize to rational multiples of `g β 0`, leaving no seed ratio.
The proof establishes nonzero denominators and substitutes the exact
coefficient identities before rational simplification.
-/
noncomputable section
namespace KsIndex.Stage2GrpAoNeg
open KsIndex.CircleQ KsIndex.PowerArc KsIndex.OppositeHalf KsIndex.AlphaRemarkTrial

set_option linter.style.longLine false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

private lemma fAoA1_m4 : g (2161809/5000000:ℝ) (-4) / g (2161809/5000000:ℝ) 0 = (-16944671847519/269527688152481 : ℝ) := by
  rw [show ((-4:ℝ)) = ((-4:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (-4:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fAoB_m4 : g (2161809/5000000:ℝ) (-4) = g (2161809/5000000:ℝ) 0 * (-16944671847519/269527688152481 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fAoA1_m4

private lemma fAoA1_m2 : g (2161809/5000000:ℝ) (-2) / g (2161809/5000000:ℝ) 0 = (2161809/12161809 : ℝ) := by
  rw [show ((-2:ℝ)) = ((-2:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (-2:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fAoB_m2 : g (2161809/5000000:ℝ) (-2) = g (2161809/5000000:ℝ) 0 * (2161809/12161809 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fAoA1_m2

private lemma fAoA1_0 : g (2161809/5000000:ℝ) 0 / g (2161809/5000000:ℝ) 0 = (1:ℝ) := div_self (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'

private lemma fAoA1_2 : g (2161809/5000000:ℝ) (2) / g (2161809/5000000:ℝ) 0 = (2161809/12161809 : ℝ) := by
  rw [show ((2:ℝ)) = ((2:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (2:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fAoB_2 : g (2161809/5000000:ℝ) (2) = g (2161809/5000000:ℝ) 0 * (2161809/12161809 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fAoA1_2

private lemma fAoA1_4 : g (2161809/5000000:ℝ) (4) / g (2161809/5000000:ℝ) 0 = (-16944671847519/269527688152481 : ℝ) := by
  rw [show ((4:ℝ)) = ((4:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (4:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fAoB_4 : g (2161809/5000000:ℝ) (4) = g (2161809/5000000:ℝ) 0 * (-16944671847519/269527688152481 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fAoA1_4

private lemma fAoA1_6 : g (2161809/5000000:ℝ) (6) / g (2161809/5000000:ℝ) 0 = (100754097616122266043/2889499342190552266043 : ℝ) := by
  rw [show ((6:ℝ)) = ((6:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (6:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fAoB_6 : g (2161809/5000000:ℝ) (6) = g (2161809/5000000:ℝ) 0 * (100754097616122266043/2889499342190552266043 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fAoA1_6

private lemma fAoA1_8 : g (2161809/5000000:ℝ) (8) / g (2161809/5000000:ℝ) 0 = (-2804811813470256321457848213/121826519371063706245422151787 : ℝ) := by
  rw [show ((8:ℝ)) = ((8:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (8:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fAoB_8 : g (2161809/5000000:ℝ) (8) = g (2161809/5000000:ℝ) 0 * (-2804811813470256321457848213/121826519371063706245422151787 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fAoA1_8

private lemma fAoA1_10 : g (2161809/5000000:ℝ) (10) / g (2161809/5000000:ℝ) 0 = (15161286445306275930039922733214669/907813090652603596000831057983214669 : ℝ) := by
  rw [show ((10:ℝ)) = ((10:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (10:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fAoB_10 : g (2161809/5000000:ℝ) (10) = g (2161809/5000000:ℝ) 0 * (15161286445306275930039922733214669/907813090652603596000831057983214669 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fAoA1_10

private lemma fAoA1_12 : g (2161809/5000000:ℝ) (12) / g (2161809/5000000:ℝ) 0 = (-241762838925424227146650820445588459874593/18810434649615610029105608022540171820125407 : ℝ) := by
  rw [show ((12:ℝ)) = ((12:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (12:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fAoB_12 : g (2161809/5000000:ℝ) (12) = g (2161809/5000000:ℝ) 0 * (-241762838925424227146650820445588459874593/18810434649615610029105608022540171820125407 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fAoA1_12

private lemma fAoA1_14 : g (2161809/5000000:ℝ) (14) / g (2161809/5000000:ℝ) 0 = (13983125254470921205735375163238650449622545981263/1357394992392543574338803326951411573711071975981263 : ℝ) := by
  rw [show ((14:ℝ)) = ((14:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (14:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fAoB_14 : g (2161809/5000000:ℝ) (14) = g (2161809/5000000:ℝ) 0 * (13983125254470921205735375163238650449622545981263/1357394992392543574338803326951411573711071975981263 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fAoA1_14

theorem bridge_grpAo_neg (n : ℝ) (hn : 3 ≤ n) :
    n * (6*(∑ i ∈ grpAo, endpointMassPos i) + 2*demodGroupPos grpAo n
        - (6*n-1-4/(6*n-1))*groupCorrectionRatR grpAo (4323618/10000000) 14 (n+9/2))
      = GroupBounds.grpValue_0_1_m n := by
  have hden := GroupBounds.grpDen_0_1_m_ne_zero n hn
  have hg0 : g (2161809/5000000:ℝ) 0 ≠ 0 :=
    (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
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
  have hb0 : (10000000 * (n * 2 + 9 + 2) - 2 * 67838191 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < 10000000 * (n * 2 + 9 + 2) - 2 * 67838191).ne'
  have hb1 : (10000000 * (n * 2 + 9 + 2 + 2) - 2 * 67838191 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < 10000000 * (n * 2 + 9 + 2 + 2) - 2 * 67838191).ne'
  have hb2 : (10000000 * (n * 2 + 9 + 2 ^ 2 + 2) - 2 * 67838191 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < 10000000 * (n * 2 + 9 + 2 ^ 2 + 2) - 2 * 67838191).ne'
  have hb3 : (10000000 * (n * 2 + 9 + 2 * 3 + 2) - 2 * 67838191 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < 10000000 * (n * 2 + 9 + 2 * 3 + 2) - 2 * 67838191).ne'
  have hb4 : (10000000 * (n * 2 + 9 + 2 * 4 + 2) - 2 * 67838191 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < 10000000 * (n * 2 + 9 + 2 * 4 + 2) - 2 * 67838191).ne'
  unfold GroupBounds.grpValue_0_1_m
  rw [eq_div_iff hden]
  unfold demodGroupPos groupCorrectionRatR rationalGroupRest rationalCorrectionUnit trialGroupMultR
  simp [grpAo, Finset.sum_filter, Fin.sum_univ_succ, Finset.sum_range_succ, endpointMassPos,
    coefficient, exponent, shift, chainLenR, baseShift, zChainForceUnit, zChainCoeff,
    GroupBounds.grpNum_0_1_m, GroupBounds.grpDen_0_1_m]
  norm_num only
  simp only [fAoB_m4, fAoB_m2, fAoB_2, fAoB_4, fAoB_6, fAoB_8, fAoB_10, fAoB_12, fAoB_14, fAoA1_0]
  norm_num [normalizedCoefficient]
  field_simp
  ring

end KsIndex.Stage2GrpAoNeg

#print axioms KsIndex.Stage2GrpAoNeg.bridge_grpAo_neg
