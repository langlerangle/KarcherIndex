module

public import KsIndexLean.AlphaLowModeEnergy

@[expose] public section

namespace KsIndex.AlphaRemarkTrial
open CircleQ AlphaResidual
set_option maxHeartbeats 4000000

theorem scalar_m2
    (hC : lowLinearNumerator (Finset.Ico (-16385) 16385) (-2) = 1209655575089421577956940153462869826420658695024544)
    (hE : lowLinearRadius (Finset.Ico (-16385) 16385) (-2) = 17673267645876280196494995410394483995691792) :
    -(1/2500 : ℝ) ≤ lowResidualCenter (-2)-lowResidualError (-2) ∧
    lowResidualCenter (-2)+lowResidualError (-2) ≤ (1/2500 : ℝ) := by
  have hs : sampleNumerator (-4) = -111606487265029559071746835857413488498704320384686 ∧ sampleRadius (-4) = 770391616179637050877709571628205521858820 := by decide +kernel
  have hpL : (314159265358979 : ℝ)/100000000000000 ≤ Real.pi := by
    linarith [Real.pi_gt_d20]
  have hpU : Real.pi ≤ (314159265358980 : ℝ)/100000000000000 := by
    linarith [Real.pi_lt_d20]
  have hL := one_div_le_one_div_of_le Real.pi_pos hpU
  have hU := one_div_le_one_div_of_le
    (by norm_num : (0 : ℝ) < 314159265358979/100000000000000) hpL
  norm_num [one_div] at hL hU
  unfold lowResidualCenter lowResidualError
  rw [hC, hE]
  norm_num [innerError16385, innerPairAMajorant, innerPairBMajorant,
    AlphaRemark.spectralUpper, sigP, hs.1, hs.2, div_eq_mul_inv]
  constructor <;> linarith [hL, hU]

theorem scalar_m1
    (hC : lowLinearNumerator (Finset.Ico (-16385) 16385) (-1) = -1820970240347663089127427786013456132150685939830498)
    (hE : lowLinearRadius (Finset.Ico (-16385) 16385) (-1) = 15817915330266250446056156811935938276986659) :
    -(1/2500 : ℝ) ≤ lowResidualCenter (-1)-lowResidualError (-1) ∧
    lowResidualCenter (-1)+lowResidualError (-1) ≤ (1/2500 : ℝ) := by
  have hs : sampleNumerator (-2) = 424830427850324224989719710307639519984977397498970 ∧ sampleRadius (-2) = 2432772908539281562553655647163799815859440 := by decide +kernel
  have hpL : (314159265358979 : ℝ)/100000000000000 ≤ Real.pi := by
    linarith [Real.pi_gt_d20]
  have hpU : Real.pi ≤ (314159265358980 : ℝ)/100000000000000 := by
    linarith [Real.pi_lt_d20]
  have hL := one_div_le_one_div_of_le Real.pi_pos hpU
  have hU := one_div_le_one_div_of_le
    (by norm_num : (0 : ℝ) < 314159265358979/100000000000000) hpL
  norm_num [one_div] at hL hU
  unfold lowResidualCenter lowResidualError
  rw [hC, hE]
  norm_num [innerError16385, innerPairAMajorant, innerPairBMajorant,
    AlphaRemark.spectralUpper, sigP, hs.1, hs.2, div_eq_mul_inv]
  constructor <;> linarith [hL, hU]

theorem scalar_p1
    (hC : lowLinearNumerator (Finset.Ico (-16385) 16385) (1) = -480076729197510562085811046592159196912728328516276)
    (hE : lowLinearRadius (Finset.Ico (-16385) 16385) (1) = 20500126803443151255103466390433874869569972) :
    -(1/2500 : ℝ) ≤ lowResidualCenter (1)-lowResidualError (1) ∧
    lowResidualCenter (1)+lowResidualError (1) ≤ (1/2500 : ℝ) := by
  have hs : sampleNumerator (2) = 73790864248318007025008910757455004820953101708776 ∧ sampleRadius (2) = 2432772908539281562553655647163799815859440 := by decide +kernel
  have hpL : (314159265358979 : ℝ)/100000000000000 ≤ Real.pi := by
    linarith [Real.pi_gt_d20]
  have hpU : Real.pi ≤ (314159265358980 : ℝ)/100000000000000 := by
    linarith [Real.pi_lt_d20]
  have hL := one_div_le_one_div_of_le Real.pi_pos hpU
  have hU := one_div_le_one_div_of_le
    (by norm_num : (0 : ℝ) < 314159265358979/100000000000000) hpL
  norm_num [one_div] at hL hU
  unfold lowResidualCenter lowResidualError
  rw [hC, hE]
  norm_num [innerError16385, innerPairAMajorant, innerPairBMajorant,
    AlphaRemark.spectralUpper, sigP, hs.1, hs.2, div_eq_mul_inv]
  constructor <;> linarith [hL, hU]

theorem scalar_p2
    (hC : lowLinearNumerator (Finset.Ico (-16385) 16385) (2) = 267583398606473793386616803577987409939721331059893)
    (hE : lowLinearRadius (Finset.Ico (-16385) 16385) (2) = 20588095017505324485377527922342464578857064) :
    -(1/2500 : ℝ) ≤ lowResidualCenter (2)-lowResidualError (2) ∧
    lowResidualCenter (2)+lowResidualError (2) ≤ (1/2500 : ℝ) := by
  have hs : sampleNumerator (4) = -21019707821796521885150519509592437742206556578042 ∧ sampleRadius (4) = 770391616179637050877709571628205521858820 := by decide +kernel
  have hpL : (314159265358979 : ℝ)/100000000000000 ≤ Real.pi := by
    linarith [Real.pi_gt_d20]
  have hpU : Real.pi ≤ (314159265358980 : ℝ)/100000000000000 := by
    linarith [Real.pi_lt_d20]
  have hL := one_div_le_one_div_of_le Real.pi_pos hpU
  have hU := one_div_le_one_div_of_le
    (by norm_num : (0 : ℝ) < 314159265358979/100000000000000) hpL
  norm_num [one_div] at hL hU
  unfold lowResidualCenter lowResidualError
  rw [hC, hE]
  norm_num [innerError16385, innerPairAMajorant, innerPairBMajorant,
    AlphaRemark.spectralUpper, sigP, hs.1, hs.2, div_eq_mul_inv]
  constructor <;> linarith [hL, hU]


/-- The four center/radius certificate pairs suffice for the low-window allocation. -/
theorem low_energy_of_linear_certificates
    (hm2C : lowLinearNumerator (Finset.Ico (-16385) 16385) (-2) = 1209655575089421577956940153462869826420658695024544)
    (hm2E : lowLinearRadius (Finset.Ico (-16385) 16385) (-2) = 17673267645876280196494995410394483995691792)
    (hm1C : lowLinearNumerator (Finset.Ico (-16385) 16385) (-1) = -1820970240347663089127427786013456132150685939830498)
    (hm1E : lowLinearRadius (Finset.Ico (-16385) 16385) (-1) = 15817915330266250446056156811935938276986659)
    (hp1C : lowLinearNumerator (Finset.Ico (-16385) 16385) (1) = -480076729197510562085811046592159196912728328516276)
    (hp1E : lowLinearRadius (Finset.Ico (-16385) 16385) (1) = 20500126803443151255103466390433874869569972)
    (hp2C : lowLinearNumerator (Finset.Ico (-16385) 16385) (2) = 267583398606473793386616803577987409939721331059893)
    (hp2E : lowLinearRadius (Finset.Ico (-16385) 16385) (2) = 20588095017505324485377527922342464578857064)
    : (∑ n ∈ residualWindow 2,
      realResidual AlphaRemark.spectralUpper n^2/residualWeight n) ≤
        (1/10000000 : ℝ) := by
  apply low_energy_of_center_bounds
  intro n hn
  have hm := (mem_residualWindow 2 n).mp hn
  have cases : n = -2 ∨ n = -1 ∨ n = 1 ∨ n = 2 := by
    rw [abs_le] at hm
    omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact scalar_m2 hm2C hm2E
  · exact scalar_m1 hm1C hm1E
  · exact scalar_p1 hp1C hp1E
  · exact scalar_p2 hp2C hp2E

end KsIndex.AlphaRemarkTrial
