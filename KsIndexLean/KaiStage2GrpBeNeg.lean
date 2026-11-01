module

public import KsIndexLean.AlphaRemainderIdentity
public import KsIndexLean.AlphaGroupDenomPositive

@[expose] public section


/-! Exact identification for the reflected family-B, even-shift group.

At `β = 2838191/5000000`, the required odd-frequency values of `g β`
are rational multiples of `g β 1`. For real `n ≥ 3`, the main theorem
identifies the scaled expression formed from `endpointMassPos`, `demodGroupPos` and `groupCorrectionRatR`
with `(g β 1 / g β 0) * GroupBounds.grpValue_1_0_m n`.

The correction uses frequency 15 and the factor `6*n-1 - 4/(6*n-1)`.
The private coefficient identities and nonzero denominator facts reduce
this equality to rational algebra; the seed ratio remains explicit.
-/
noncomputable section
namespace KsIndex.Stage2GrpBeNeg
open KsIndex.CircleQ KsIndex.PowerArc KsIndex.OppositeHalf KsIndex.AlphaRemarkTrial

set_option linter.style.longLine false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

private lemma fBe_m5 : g (2838191/5000000:ℝ) (-5) = g (2838191/5000000:ℝ) 1 * (8763836050827/165527656050827 : ℝ) := by
  have h0 : g (2838191/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2838191/5000000) le_rfl zero_le_one).ne'
  have key : g (2838191/5000000:ℝ) ((-5:ℤ):ℝ) / g (2838191/5000000:ℝ) 0 = g (2838191/5000000:ℝ) 1 / g (2838191/5000000:ℝ) 0 * (8763836050827/165527656050827 : ℝ) := by
    rw [normalized_g_integer_seed (by norm_num : (0:ℝ) < 2838191/5000000) (-5:ℤ)]
    norm_num [integerSeedValue, normalizedCoefficient]
  rw [show ((-5:ℤ):ℝ) = (-5:ℝ) by norm_num] at key
  rw [div_mul_eq_mul_div, div_eq_div_iff h0 h0] at key
  exact mul_right_cancel₀ h0 key

private lemma fBe_m3 : g (2838191/5000000:ℝ) (-3) = g (2838191/5000000:ℝ) 1 * (-2161809/17838191 : ℝ) := by
  have h0 : g (2838191/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2838191/5000000) le_rfl zero_le_one).ne'
  have key : g (2838191/5000000:ℝ) ((-3:ℤ):ℝ) / g (2838191/5000000:ℝ) 0 = g (2838191/5000000:ℝ) 1 / g (2838191/5000000:ℝ) 0 * (-2161809/17838191 : ℝ) := by
    rw [normalized_g_integer_seed (by norm_num : (0:ℝ) < 2838191/5000000) (-3:ℤ)]
    norm_num [integerSeedValue, normalizedCoefficient]
  rw [show ((-3:ℤ):ℝ) = (-3:ℝ) by norm_num] at key
  rw [div_mul_eq_mul_div, div_eq_div_iff h0 h0] at key
  exact mul_right_cancel₀ h0 key

private lemma fBe_m1 : g (2838191/5000000:ℝ) (-1) = g (2838191/5000000:ℝ) 1 * (1 : ℝ) := by
  have h0 : g (2838191/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2838191/5000000) le_rfl zero_le_one).ne'
  have key : g (2838191/5000000:ℝ) ((-1:ℤ):ℝ) / g (2838191/5000000:ℝ) 0 = g (2838191/5000000:ℝ) 1 / g (2838191/5000000:ℝ) 0 * (1 : ℝ) := by
    rw [normalized_g_integer_seed (by norm_num : (0:ℝ) < 2838191/5000000) (-1:ℤ)]
    norm_num [integerSeedValue, normalizedCoefficient]
  rw [show ((-1:ℤ):ℝ) = (-1:ℝ) by norm_num] at key
  rw [div_mul_eq_mul_div, div_eq_div_iff h0 h0] at key
  exact mul_right_cancel₀ h0 key

private lemma fBe_3 : g (2838191/5000000:ℝ) (3) = g (2838191/5000000:ℝ) 1 * (-2161809/17838191 : ℝ) := by
  have h0 : g (2838191/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2838191/5000000) le_rfl zero_le_one).ne'
  have key : g (2838191/5000000:ℝ) ((3:ℤ):ℝ) / g (2838191/5000000:ℝ) 0 = g (2838191/5000000:ℝ) 1 / g (2838191/5000000:ℝ) 0 * (-2161809/17838191 : ℝ) := by
    rw [normalized_g_integer_seed (by norm_num : (0:ℝ) < 2838191/5000000) (3:ℤ)]
    norm_num [integerSeedValue, normalizedCoefficient]
  rw [show ((3:ℤ):ℝ) = (3:ℝ) by norm_num] at key
  rw [div_mul_eq_mul_div, div_eq_div_iff h0 h0] at key
  exact mul_right_cancel₀ h0 key

private lemma fBe_5 : g (2838191/5000000:ℝ) (5) = g (2838191/5000000:ℝ) 1 * (8763836050827/165527656050827 : ℝ) := by
  have h0 : g (2838191/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2838191/5000000) le_rfl zero_le_one).ne'
  have key : g (2838191/5000000:ℝ) ((5:ℤ):ℝ) / g (2838191/5000000:ℝ) 0 = g (2838191/5000000:ℝ) 1 / g (2838191/5000000:ℝ) 0 * (8763836050827/165527656050827 : ℝ) := by
    rw [normalized_g_integer_seed (by norm_num : (0:ℝ) < 2838191/5000000) (5:ℤ)]
    norm_num [integerSeedValue, normalizedCoefficient]
  rw [show ((5:ℤ):ℝ) = (5:ℝ) by norm_num] at key
  rw [div_mul_eq_mul_div, div_eq_div_iff h0 h0] at key
  exact mul_right_cancel₀ h0 key

private lemma fBe_7 : g (2838191/5000000:ℝ) (7) = g (2838191/5000000:ℝ) 1 * (-194222460665742266043/6263267065433497733957 : ℝ) := by
  have h0 : g (2838191/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2838191/5000000) le_rfl zero_le_one).ne'
  have key : g (2838191/5000000:ℝ) ((7:ℤ):ℝ) / g (2838191/5000000:ℝ) 0 = g (2838191/5000000:ℝ) 1 / g (2838191/5000000:ℝ) 0 * (-194222460665742266043/6263267065433497733957 : ℝ) := by
    rw [normalized_g_integer_seed (by norm_num : (0:ℝ) < 2838191/5000000) (7:ℤ)]
    norm_num [integerSeedValue, normalizedCoefficient]
  rw [show ((7:ℤ):ℝ) = (7:ℝ) by norm_num] at key
  rw [div_mul_eq_mul_div, div_eq_div_iff h0 h0] at key
  exact mul_right_cancel₀ h0 key

private lemma fBe_9 : g (2838191/5000000:ℝ) (9) = g (2838191/5000000:ℝ) 1 * (6246545683441615603702151787/299623366160217162395102151787 : ℝ) := by
  have h0 : g (2838191/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2838191/5000000) le_rfl zero_le_one).ne'
  have key : g (2838191/5000000:ℝ) ((9:ℤ):ℝ) / g (2838191/5000000:ℝ) 0 = g (2838191/5000000:ℝ) 1 / g (2838191/5000000:ℝ) 0 * (6246545683441615603702151787/299623366160217162395102151787 : ℝ) := by
    rw [normalized_g_integer_seed (by norm_num : (0:ℝ) < 2838191/5000000) (9:ℤ)]
    norm_num [integerSeedValue, normalizedCoefficient]
  rw [show ((9:ℤ):ℝ) = (9:ℝ) by norm_num] at key
  rw [div_mul_eq_mul_div, div_eq_div_iff h0 h0] at key
  exact mul_right_cancel₀ h0 key

private lemma fBe_11 : g (2838191/5000000:ℝ) (11) = g (2838191/5000000:ℝ) 1 * (-87788555338346619911569938844167561/5776557826679192280028645239855832439 : ℝ) := by
  have h0 : g (2838191/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2838191/5000000) le_rfl zero_le_one).ne'
  have key : g (2838191/5000000:ℝ) ((11:ℤ):ℝ) / g (2838191/5000000:ℝ) 0 = g (2838191/5000000:ℝ) 1 / g (2838191/5000000:ℝ) 0 * (-87788555338346619911569938844167561/5776557826679192280028645239855832439 : ℝ) := by
    rw [normalized_g_integer_seed (by norm_num : (0:ℝ) < 2838191/5000000) (11:ℤ)]
    norm_num [integerSeedValue, normalizedCoefficient]
  rw [show ((11:ℤ):ℝ) = (11:ℝ) by norm_num] at key
  rw [div_mul_eq_mul_div, div_eq_div_iff h0 h0] at key
  exact mul_right_cancel₀ h0 key

private lemma fBe_13 : g (2838191/5000000:ℝ) (13) = g (2838191/5000000:ℝ) 1 * (654172836563538109088986862875878440125407/55981604738401134516901245893225824780125407 : ℝ) := by
  have h0 : g (2838191/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2838191/5000000) le_rfl zero_le_one).ne'
  have key : g (2838191/5000000:ℝ) ((13:ℤ):ℝ) / g (2838191/5000000:ℝ) 0 = g (2838191/5000000:ℝ) 1 / g (2838191/5000000:ℝ) 0 * (654172836563538109088986862875878440125407/55981604738401134516901245893225824780125407 : ℝ) := by
    rw [normalized_g_integer_seed (by norm_num : (0:ℝ) < 2838191/5000000) (13:ℤ)]
    norm_num [integerSeedValue, normalizedCoefficient]
  rw [show ((13:ℤ):ℝ) = (13:ℝ) by norm_num] at key
  rw [div_mul_eq_mul_div, div_eq_div_iff h0 h0] at key
  exact mul_right_cancel₀ h0 key

private lemma fBe_15 : g (2838191/5000000:ℝ) (15) = g (2838191/5000000:ℝ) 1 * (-40664566919450872301410765373599546302293485981263/4357506842114172543143251905974877355367934434018737 : ℝ) := by
  have h0 : g (2838191/5000000:ℝ) 0 ≠ 0 := (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2838191/5000000) le_rfl zero_le_one).ne'
  have key : g (2838191/5000000:ℝ) ((15:ℤ):ℝ) / g (2838191/5000000:ℝ) 0 = g (2838191/5000000:ℝ) 1 / g (2838191/5000000:ℝ) 0 * (-40664566919450872301410765373599546302293485981263/4357506842114172543143251905974877355367934434018737 : ℝ) := by
    rw [normalized_g_integer_seed (by norm_num : (0:ℝ) < 2838191/5000000) (15:ℤ)]
    norm_num [integerSeedValue, normalizedCoefficient]
  rw [show ((15:ℤ):ℝ) = (15:ℝ) by norm_num] at key
  rw [div_mul_eq_mul_div, div_eq_div_iff h0 h0] at key
  exact mul_right_cancel₀ h0 key

theorem bridge_grpBe_neg (n : ℝ) (hn : 3 ≤ n) :
    n * (6*(∑ i ∈ grpBe, endpointMassPos i) + 2*demodGroupPos grpBe n
        - (6*n-1-4/(6*n-1))*groupCorrectionRatR grpBe (5676382/10000000) 15 (n+9/2))
      = (g (2838191/5000000:ℝ) 1 / g (2838191/5000000:ℝ) 0) * GroupBounds.grpValue_1_0_m n := by
  have hden := GroupBounds.grpDen_1_0_m_ne_zero n hn
  have hg0 : g (2838191/5000000:ℝ) 0 ≠ 0 :=
    (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2838191/5000000) le_rfl zero_le_one).ne'
  have hg1 : g (2838191/5000000:ℝ) 1 ≠ 0 :=
    (g_pos_of_mem_unit (by norm_num : (0:ℝ) < 2838191/5000000) zero_le_one le_rfl).ne'
  have z0 : (n+9/2:ℝ) ≠ 0 := by positivity
  have z1 : (n+9/2+1:ℝ) ≠ 0 := by positivity
  have z2 : (n+9/2+2:ℝ) ≠ 0 := by positivity
  have z3 : (n+9/2+3:ℝ) ≠ 0 := by positivity
  have z4 : (n+9/2+4:ℝ) ≠ 0 := by positivity
  have z5 : (n+9/2+5:ℝ) ≠ 0 := by positivity
  have h6 : (n*6-1:ℝ) ≠ 0 := (by nlinarith [hn] : (0:ℝ) < n*6-1).ne'
  have p1 : (2*n+1:ℝ) ≠ 0 := by positivity
  have p3 : (2*n+3:ℝ) ≠ 0 := by positivity
  have p5 : (2*n+5:ℝ) ≠ 0 := by positivity
  have p7 : (2*n+7:ℝ) ≠ 0 := by positivity
  have hb0 : (10000000 * (n * 2 + 9 + 2) - 2 * 72161809 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < 10000000 * (n * 2 + 9 + 2) - 2 * 72161809).ne'
  have hb1 : (10000000 * (n * 2 + 9 + 2 + 2) - 2 * 72161809 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < 10000000 * (n * 2 + 9 + 2 + 2) - 2 * 72161809).ne'
  have hb2 : (10000000 * (n * 2 + 9 + 2 ^ 2 + 2) - 2 * 72161809 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < 10000000 * (n * 2 + 9 + 2 ^ 2 + 2) - 2 * 72161809).ne'
  have hb3 : (10000000 * (n * 2 + 9 + 2 * 3 + 2) - 2 * 72161809 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < 10000000 * (n * 2 + 9 + 2 * 3 + 2) - 2 * 72161809).ne'
  have hb4 : (10000000 * (n * 2 + 9 + 2 * 4 + 2) - 2 * 72161809 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < 10000000 * (n * 2 + 9 + 2 * 4 + 2) - 2 * 72161809).ne'
  have hb5 : (10000000 * (n * 2 + 9 + 2 * 5 + 2) - 2 * 72161809 : ℝ) ≠ 0 :=
    (by nlinarith [hn] : (0:ℝ) < 10000000 * (n * 2 + 9 + 2 * 5 + 2) - 2 * 72161809).ne'
  unfold GroupBounds.grpValue_1_0_m
  rw [← mul_div_assoc, eq_div_iff hden]
  unfold demodGroupPos groupCorrectionRatR rationalGroupRest rationalCorrectionUnit trialGroupMultR
  simp [grpBe, Finset.sum_filter, Fin.sum_univ_succ, Finset.sum_range_succ, endpointMassPos,
    coefficient, exponent, shift, chainLenR, baseShift, zChainForceUnit, zChainCoeff,
    GroupBounds.grpNum_1_0_m, GroupBounds.grpDen_1_0_m]
  norm_num only
  simp only [fBe_m5, fBe_m3, fBe_m1, fBe_3, fBe_5, fBe_7, fBe_9, fBe_11, fBe_13, fBe_15]
  norm_num [normalizedCoefficient]
  field_simp
  ring

end KsIndex.Stage2GrpBeNeg

#print axioms KsIndex.Stage2GrpBeNeg.bridge_grpBe_neg
