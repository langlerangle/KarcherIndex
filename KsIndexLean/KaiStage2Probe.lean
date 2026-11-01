module

public import KsIndexLean.AlphaRemainderIdentity
public import KsIndexLean.AlphaGroupDenomPositive

@[expose] public section


/-! Exact rational identification for the family-A, odd-shift group.

At `β = 2161809/5000000`, the required even-frequency values of `g β`
are rational multiples of `g β 0`. For real `n ≥ 3`, `bridge_grpAo`
identifies the scaled endpoint-mass, demodulated-group and correction
expression with `GroupBounds.grpValue_0_1_p n`, leaving no seed ratio.

The proof first normalizes the literal frequency arguments, then rewrites
with the private coefficient identities. Nonzero denominator facts permit
the final rational-algebra simplification.
-/
noncomputable section
namespace KsIndex.Stage2Probe
open KsIndex.CircleQ KsIndex.PowerArc KsIndex.OppositeHalf KsIndex.AlphaRemarkTrial

set_option linter.style.longLine false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

private lemma fA1_m4 : g (2161809/5000000:ℝ) (-4) / g (2161809/5000000:ℝ) 0 = (-16944671847519 / 269527688152481 : ℝ) := by
  rw [show ((-4:ℝ)) = ((-4:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (-4:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fA1_m2 : g (2161809/5000000:ℝ) (-2) / g (2161809/5000000:ℝ) 0 = (2161809 / 12161809 : ℝ) := by
  rw [show ((-2:ℝ)) = ((-2:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (-2:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fA1_0 : g (2161809/5000000:ℝ) (0) / g (2161809/5000000:ℝ) 0 = (1 : ℝ) :=
  div_self (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'

private lemma fA1_2 : g (2161809/5000000:ℝ) (2) / g (2161809/5000000:ℝ) 0 = (2161809 / 12161809 : ℝ) := by
  rw [show ((2:ℝ)) = ((2:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (2:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fA1_4 : g (2161809/5000000:ℝ) (4) / g (2161809/5000000:ℝ) 0 = (-16944671847519 / 269527688152481 : ℝ) := by
  rw [show ((4:ℝ)) = ((4:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (4:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fA1_6 : g (2161809/5000000:ℝ) (6) / g (2161809/5000000:ℝ) 0 = (100754097616122266043 / 2889499342190552266043 : ℝ) := by
  rw [show ((6:ℝ)) = ((6:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (6:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fA1_8 : g (2161809/5000000:ℝ) (8) / g (2161809/5000000:ℝ) 0 = (-2804811813470256321457848213 / 121826519371063706245422151787 : ℝ) := by
  rw [show ((8:ℝ)) = ((8:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (8:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fA1_10 : g (2161809/5000000:ℝ) (10) / g (2161809/5000000:ℝ) 0 = (15161286445306275930039922733214669 / 907813090652603596000831057983214669 : ℝ) := by
  rw [show ((10:ℝ)) = ((10:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (10:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fA1_12 : g (2161809/5000000:ℝ) (12) / g (2161809/5000000:ℝ) 0 = (-241762838925424227146650820445588459874593 / 18810434649615610029105608022540171820125407 : ℝ) := by
  rw [show ((12:ℝ)) = ((12:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (12:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]

private lemma fA1_14 : g (2161809/5000000:ℝ) (14) / g (2161809/5000000:ℝ) 0 = (13983125254470921205735375163238650449622545981263 / 1357394992392543574338803326951411573711071975981263 : ℝ) := by
  rw [show ((14:ℝ)) = ((14:ℤ):ℝ) by norm_num,
      normalized_g_integer_seed (by norm_num : (0:ℝ) < 2161809/5000000) (14:ℤ)]
  norm_num [integerSeedValue, normalizedCoefficient]


private lemma fB_m4 : g (2161809/5000000:ℝ) (-4) = g (2161809/5000000:ℝ) 0 * (-16944671847519 / 269527688152481 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fA1_m4

private lemma fB_m2 : g (2161809/5000000:ℝ) (-2) = g (2161809/5000000:ℝ) 0 * (2161809 / 12161809 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fA1_m2

private lemma fB_2 : g (2161809/5000000:ℝ) (2) = g (2161809/5000000:ℝ) 0 * (2161809 / 12161809 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fA1_2

private lemma fB_4 : g (2161809/5000000:ℝ) (4) = g (2161809/5000000:ℝ) 0 * (-16944671847519 / 269527688152481 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fA1_4

private lemma fB_6 : g (2161809/5000000:ℝ) (6) = g (2161809/5000000:ℝ) 0 * (100754097616122266043 / 2889499342190552266043 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fA1_6

private lemma fB_8 : g (2161809/5000000:ℝ) (8) = g (2161809/5000000:ℝ) 0 * (-2804811813470256321457848213 / 121826519371063706245422151787 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fA1_8

private lemma fB_10 : g (2161809/5000000:ℝ) (10) = g (2161809/5000000:ℝ) 0 * (15161286445306275930039922733214669 / 907813090652603596000831057983214669 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fA1_10

private lemma fB_12 : g (2161809/5000000:ℝ) (12) = g (2161809/5000000:ℝ) 0 * (-241762838925424227146650820445588459874593 / 18810434649615610029105608022540171820125407 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fA1_12

private lemma fB_14 : g (2161809/5000000:ℝ) (14) = g (2161809/5000000:ℝ) 0 * (13983125254470921205735375163238650449622545981263 / 1357394992392543574338803326951411573711071975981263 : ℝ) := by
  have h0 : g (2161809/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  rw [mul_comm, ← div_eq_iff h0]; exact fA1_14

theorem bridge_grpAo (n : ℝ) (hn : 3 ≤ n) :
    n * (6*(∑ i ∈ grpAo, endpointMass i) + 2*demodGroup grpAo n
        - (6*n+1-4/(6*n+1))*groupCorrectionRat grpAo (4323618/10000000) 14 (n+9/2))
      = GroupBounds.grpValue_0_1_p n := by
  have hden := GroupBounds.grpDen_0_1_p_ne_zero n hn
  have a1p : (0:ℝ) < 14323618 + n * 20000000 := by nlinarith [hn]
  have a2p : (0:ℝ) < 34323618 + n * 20000000 := by nlinarith [hn]
  have a3p : (0:ℝ) < -5676382 + n * 20000000 := by nlinarith [hn]
  have a4p : (0:ℝ) < 54323618 + n * 20000000 := by nlinarith [hn]
  have a5p : (0:ℝ) < -25676382 + n * 20000000 := by nlinarith [hn]
  have aqp : (0:ℝ) < 145748952609924 - n * 627055280000000 + n ^ 2 * 400000000000000 := by
    nlinarith [mul_pos a5p a3p]
  have z0 : (n+9/2:ℝ) ≠ 0 := by positivity
  have z1 : (n+9/2+1:ℝ) ≠ 0 := by positivity
  have z2 : (n+9/2+2:ℝ) ≠ 0 := by positivity
  have z3 : (n+9/2+3:ℝ) ≠ 0 := by positivity
  have z4 : (n+9/2+4:ℝ) ≠ 0 := by positivity
  have h6 : (6*n+1:ℝ) ≠ 0 := by positivity
  have p1 : (2*n+1:ℝ) ≠ 0 := by positivity
  have p3 : (2*n+3:ℝ) ≠ 0 := by positivity
  have p5 : (2*n+5:ℝ) ≠ 0 := by positivity
  have p7 : (2*n+7:ℝ) ≠ 0 := by positivity
  have a1 := a1p.ne'
  have a2 := a2p.ne'
  have a3 := a3p.ne'
  have a4 := a4p.ne'
  have a5 := a5p.ne'
  have aq := aqp.ne'
  have hg0 : g (2161809/5000000:ℝ) 0 ≠ 0 :=
    (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2161809/5000000) le_rfl zero_le_one).ne'
  have hne0 : ((n * 2 + 9 + 2) * 10000000 - 2 * 67838191 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < (n * 2 + 9 + 2) * 10000000 - 2 * 67838191).ne'
  have hne1 : (10000000 * (n * 2 + 9 + 2 + 2) - 2 * 67838191 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < 10000000 * (n * 2 + 9 + 2 + 2) - 2 * 67838191).ne'
  have hne2 : (10000000 * (n * 2 + 9 + 2 ^ 2 + 2) - 2 * 67838191 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < 10000000 * (n * 2 + 9 + 2 ^ 2 + 2) - 2 * 67838191).ne'
  have hne3 : (10000000 * (n * 2 + 9 + 2 * 3 + 2) - 2 * 67838191 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < 10000000 * (n * 2 + 9 + 2 * 3 + 2) - 2 * 67838191).ne'
  have hne4 : ((n * 2 + 9 + 2 * 4 + 2) * 10000000 - 2 * 67838191 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < (n * 2 + 9 + 2 * 4 + 2) * 10000000 - 2 * 67838191).ne'
  unfold GroupBounds.grpValue_0_1_p
  rw [eq_div_iff hden]
  unfold demodGroup groupCorrectionRat rationalGroupRest rationalCorrectionUnit trialGroupMult
  simp [grpAo, Finset.sum_filter, Fin.sum_univ_succ, Finset.sum_range_succ, endpointMass,
    coefficient, exponent, shift, chainLen, baseShift, zChainForceUnit, zChainCoeff,
    GroupBounds.grpNum_0_1_p, GroupBounds.grpDen_0_1_p]
  norm_num only
  simp only [fB_m4, fB_m2, fB_2, fB_4, fB_6, fB_8, fB_10, fB_12, fB_14, fA1_0]
  norm_num [normalizedCoefficient]
  field_simp
  ring

end KsIndex.Stage2Probe

#print axioms KsIndex.Stage2Probe.bridge_grpAo
