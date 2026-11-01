module

public import KsIndexLean.AlphaGroupSeedEnclosure
public import KsIndexLean.AlphaGroupAnchorSamples
public import KsIndexLean.AlphaOuterTailBudget

@[expose] public section


/-! Concrete compensated-group bounds at the shared energy anchor. -/
namespace KsIndex.PowerArc

theorem anchorGroup_b15_abs :
    |compensatedPowerArcGroup (2161809/5000000 : ℝ) 15
      (2*(12387581/10000000 : ℝ)^2/Real.pi) (1+(12387581/10000000 : ℝ)^2) 1024| ≤ (3/250000 : ℝ) := by
  have hh := affine_group_abs_bound
    (1+(12387581/10000000 : ℝ)^2) (2*(12387581/10000000 : ℝ)^2/Real.pi)
    (122113351373/125000000000) (152034409177398034/8653788320979307077 : ℝ)
    (g (2161809/5000000 : ℝ) 2042 / g (2161809/5000000 : ℝ) 0) (4090577/500000000000 : ℝ)
    (powerArcStieltjes (2161809/5000000 : ℝ) 15 (2057/2) / g (2161809/5000000 : ℝ) 0) (-85257617/500000000000 : ℝ)
    (g (2161809/5000000 : ℝ) 15 / g (2161809/5000000 : ℝ) 0) (-5779158047/500000000000 : ℝ)
    (1/1000000000000) (1/10000000000) (1/10000000000) (1/1000000000000) (3/250000 : ℝ)
    (by simpa only using anchorSample_b2042_error)
    (by simpa only using stieltjes_full_b15_interval)
    (by convert stieltjesInitial_b15_error using 1; norm_num)
    trial_kappa_interval (by norm_num) (by norm_num)
  rw [compensatedPowerArcGroup_seed]
  convert hh using 1; norm_num [neg_div]

theorem anchorGroup_b14_abs :
    |compensatedPowerArcGroup (2161809/5000000 : ℝ) 14
      (2*(12387581/10000000 : ℝ)^2/Real.pi) (1+(12387581/10000000 : ℝ)^2) 1024| ≤ (1/50000000 : ℝ) := by
  have hh := affine_group_abs_bound
    (1+(12387581/10000000 : ℝ)^2) (2*(12387581/10000000 : ℝ)^2/Real.pi)
    (122113351373/125000000000) (426187433097194102/25961364962937921231 : ℝ)
    (g (2161809/5000000 : ℝ) 2043 / g (2161809/5000000 : ℝ) 0) (-2531841/250000000000 : ℝ)
    (powerArcStieltjes (2161809/5000000 : ℝ) 14 (2057/2) / g (2161809/5000000 : ℝ) 0) (71426451/500000000000 : ℝ)
    (g (2161809/5000000 : ℝ) 14 / g (2161809/5000000 : ℝ) 0) (1287680201/125000000000 : ℝ)
    (1/1000000000000) (1/10000000000) (1/10000000000) (1/1000000000000) (1/50000000 : ℝ)
    (by simpa only using anchorSample_b2043_error)
    (by simpa only using stieltjes_full_b14_interval)
    (by convert stieltjesInitial_b14_error using 1; norm_num)
    trial_kappa_interval (by norm_num) (by norm_num)
  rw [compensatedPowerArcGroup_seed]
  convert hh using 1; norm_num [neg_div]

theorem anchorGroup_c15_abs :
    |compensatedPowerArcGroup (2838191/5000000 : ℝ) 15
      (2*(12387581/10000000 : ℝ)^2/Real.pi) (1+(12387581/10000000 : ℝ)^2) 1024| ≤ (1/50000000 : ℝ) := by
  have hh := affine_group_abs_bound
    (1+(12387581/10000000 : ℝ)^2) (2*(12387581/10000000 : ℝ)^2/Real.pi)
    (122113351373/125000000000) (351751012572194102/25961364962937921231 : ℝ)
    (g (2838191/5000000 : ℝ) 2042 / g (2838191/5000000 : ℝ) 0) (3849223/1000000000000 : ℝ)
    (powerArcStieltjes (2838191/5000000 : ℝ) 15 (2057/2) / g (2838191/5000000 : ℝ) 0) (-83421663/1000000000000 : ℝ)
    (g (2838191/5000000 : ℝ) 15 / g (2838191/5000000 : ℝ) 0) (-1378592951/200000000000 : ℝ)
    (1/1000000000000) (1/10000000000) (1/10000000000) (1/1000000000000) (1/50000000 : ℝ)
    (by simpa only using anchorSample_c2042_error)
    (by simpa only using stieltjes_full_c15_interval)
    (by convert stieltjesInitial_c15_error using 1; norm_num)
    trial_kappa_interval (by norm_num) (by norm_num)
  rw [compensatedPowerArcGroup_seed]
  convert hh using 1; norm_num [neg_div]

theorem anchorGroup_c14_abs :
    |compensatedPowerArcGroup (2838191/5000000 : ℝ) 14
      (2*(12387581/10000000 : ℝ)^2/Real.pi) (1+(12387581/10000000 : ℝ)^2) 1024| ≤ (1/200000 : ℝ) := by
  have hh := affine_group_abs_bound
    (1+(12387581/10000000 : ℝ)^2) (2*(12387581/10000000 : ℝ)^2/Real.pi)
    (122113351373/125000000000) (766414468548238/60516002244610539 : ℝ)
    (g (2838191/5000000 : ℝ) 2043 / g (2838191/5000000 : ℝ) 0) (-1552471/500000000000 : ℝ)
    (powerArcStieltjes (2838191/5000000 : ℝ) 14 (2057/2) / g (2838191/5000000 : ℝ) 0) (108177701/1000000000000 : ℝ)
    (g (2838191/5000000 : ℝ) 14 / g (2838191/5000000 : ℝ) 0) (9516400877/1000000000000 : ℝ)
    (1/1000000000000) (1/10000000000) (1/10000000000) (1/1000000000000) (1/200000 : ℝ)
    (by simpa only using anchorSample_c2043_error)
    (by simpa only using stieltjes_full_c14_interval)
    (by simpa only using stieltjesInitial_c14_error)
    trial_kappa_interval (by norm_num) (by norm_num)
  rw [compensatedPowerArcGroup_seed]
  convert hh using 1; norm_num [neg_div]


private theorem trial_kappa_abs_le_one :
    |2*(12387581/10000000 : ℝ)^2/Real.pi| ≤ 1 := by
  have h := abs_sub_le_iff.mp trial_kappa_interval
  rw [abs_le]
  constructor <;> linarith

theorem anchorCorrection_b15_abs :
    |stieltjesCorrectionD (2161809/5000000 : ℝ) 15 (2*(12387581/10000000 : ℝ)^2/Real.pi)| ≤ 3 := by
  have ha : |g (2161809/5000000 : ℝ) 15 / g (2161809/5000000 : ℝ) 0| ≤ (5779158097/500000000000 : ℝ) := by
    have h := stieltjesInitial_b15_error
    have ht := abs_sub_le (g (2161809/5000000 : ℝ) 15 / g (2161809/5000000 : ℝ) 0) (-5779158047/500000000000 : ℝ) 0
    norm_num only [sub_zero] at ht
    have hb := abs_le.mp h
    rw [abs_le]
    constructor <;> linarith
  have he : stieltjesCorrectionD (2161809/5000000 : ℝ) 15 (2*(12387581/10000000 : ℝ)^2/Real.pi) =
      (2*(12387581/10000000 : ℝ)^2/Real.pi) * (g (2161809/5000000 : ℝ) 15 / g (2161809/5000000 : ℝ) 0) * (624480731316391/2726945265564 : ℝ) := by
    dsimp [stieltjesCorrectionD, stieltjesCorrectionC]
    ring
  rw [he, abs_mul, abs_mul]
  have hp := mul_le_mul trial_kappa_abs_le_one ha (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  simp only [one_mul] at hp
  calc
    _ ≤ (5779158097/500000000000 : ℝ) * |(624480731316391/2726945265564 : ℝ)| :=
      mul_le_mul_of_nonneg_right hp (abs_nonneg _)
    _ ≤ 3 := by norm_num

theorem anchorCorrection_b14_abs :
    |stieltjesCorrectionD (2161809/5000000 : ℝ) 14 (2*(12387581/10000000 : ℝ)^2/Real.pi)| ≤ 3 := by
  have ha : |g (2161809/5000000 : ℝ) 14 / g (2161809/5000000 : ℝ) 0| ≤ (2575360427/250000000000 : ℝ) := by
    have h := stieltjesInitial_b14_error
    have ht := abs_sub_le (g (2161809/5000000 : ℝ) 14 / g (2161809/5000000 : ℝ) 0) (1287680201/125000000000 : ℝ) 0
    norm_num only [sub_zero] at ht
    have hb := abs_le.mp h
    rw [abs_le]
    constructor <;> linarith
  have he : stieltjesCorrectionD (2161809/5000000 : ℝ) 14 (2*(12387581/10000000 : ℝ)^2/Real.pi) =
      (2*(12387581/10000000 : ℝ)^2/Real.pi) * (g (2161809/5000000 : ℝ) 14 / g (2161809/5000000 : ℝ) 0) * (4895326581847519/24542507390076 : ℝ) := by
    dsimp [stieltjesCorrectionD, stieltjesCorrectionC]
    ring
  rw [he, abs_mul, abs_mul]
  have hp := mul_le_mul trial_kappa_abs_le_one ha (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  simp only [one_mul] at hp
  calc
    _ ≤ (2575360427/250000000000 : ℝ) * |(4895326581847519/24542507390076 : ℝ)| :=
      mul_le_mul_of_nonneg_right hp (abs_nonneg _)
    _ ≤ 3 := by norm_num

theorem anchorCorrection_c15_abs :
    |stieltjesCorrectionD (2838191/5000000 : ℝ) 15 (2*(12387581/10000000 : ℝ)^2/Real.pi)| ≤ 3 := by
  have ha : |g (2838191/5000000 : ℝ) 15 / g (2838191/5000000 : ℝ) 0| ≤ (1378592971/200000000000 : ℝ) := by
    have h := stieltjesInitial_c15_error
    have ht := abs_sub_le (g (2838191/5000000 : ℝ) 15 / g (2838191/5000000 : ℝ) 0) (-1378592951/200000000000 : ℝ) 0
    norm_num only [sub_zero] at ht
    have hb := abs_le.mp h
    rw [abs_le]
    constructor <;> linarith
  have he : stieltjesCorrectionD (2838191/5000000 : ℝ) 15 (2*(12387581/10000000 : ℝ)^2/Real.pi) =
      (2*(12387581/10000000 : ℝ)^2/Real.pi) * (g (2838191/5000000 : ℝ) 15 / g (2838191/5000000 : ℝ) 0) * (5616944671847519/24542507390076 : ℝ) := by
    dsimp [stieltjesCorrectionD, stieltjesCorrectionC]
    ring
  rw [he, abs_mul, abs_mul]
  have hp := mul_le_mul trial_kappa_abs_le_one ha (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  simp only [one_mul] at hp
  calc
    _ ≤ (1378592971/200000000000 : ℝ) * |(5616944671847519/24542507390076 : ℝ)| :=
      mul_le_mul_of_nonneg_right hp (abs_nonneg _)
    _ ≤ 3 := by norm_num

theorem anchorCorrection_c14_abs :
    |stieltjesCorrectionD (2838191/5000000 : ℝ) 14 (2*(12387581/10000000 : ℝ)^2/Real.pi)| ≤ 3 := by
  have ha : |g (2838191/5000000 : ℝ) 14 / g (2838191/5000000 : ℝ) 0| ≤ (9516400977/1000000000000 : ℝ) := by
    have h := stieltjesInitial_c14_error
    have ht := abs_sub_le (g (2838191/5000000 : ℝ) 14 / g (2838191/5000000 : ℝ) 0) (9516400877/1000000000000 : ℝ) 0
    norm_num only [sub_zero] at ht
    have hb := abs_le.mp h
    rw [abs_le]
    constructor <;> linarith
  have he : stieltjesCorrectionD (2838191/5000000 : ℝ) 14 (2*(12387581/10000000 : ℝ)^2/Real.pi) =
      (2*(12387581/10000000 : ℝ)^2/Real.pi) * (g (2838191/5000000 : ℝ) 14 / g (2838191/5000000 : ℝ) 0) * (125434478765321/629295061284 : ℝ) := by
    dsimp [stieltjesCorrectionD, stieltjesCorrectionC]
    ring
  rw [he, abs_mul, abs_mul]
  have hp := mul_le_mul trial_kappa_abs_le_one ha (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  simp only [one_mul] at hp
  calc
    _ ≤ (9516400977/1000000000000 : ℝ) * |(125434478765321/629295061284 : ℝ)| :=
      mul_le_mul_of_nonneg_right hp (abs_nonneg _)
    _ ≤ 3 := by norm_num


theorem anchorEnergy_b15 :
    KsIndex.AlphaRemarkTrial.compensatedTailEnergy (2161809/5000000 : ℝ) 15 (2*(12387581/10000000 : ℝ)^2/Real.pi) (1+(12387581/10000000 : ℝ)^2) 1023 ≤ (1/20 : ℝ)^2 := by
  have hg := anchorGroup_b15_abs
  have hd := anchorCorrection_b15_abs
  have hc : |compensatedPowerArcGroup (2161809/5000000 : ℝ) 15 (2*(12387581/10000000 : ℝ)^2/Real.pi) (1+(12387581/10000000 : ℝ)^2) 1024| +
      11*|stieltjesCorrectionD (2161809/5000000 : ℝ) 15 (2*(12387581/10000000 : ℝ)^2/Real.pi)|/(2057/2)^3 ≤ (2379730689/197810890750000 : ℝ) := by
    norm_num at hg hd ⊢
    linarith
  have hsq := sq_le_sq₀ (by positivity : (0:ℝ) ≤
    |compensatedPowerArcGroup (2161809/5000000 : ℝ) 15 (2*(12387581/10000000 : ℝ)^2/Real.pi) (1+(12387581/10000000 : ℝ)^2) 1024| +
      11*|stieltjesCorrectionD (2161809/5000000 : ℝ) 15 (2*(12387581/10000000 : ℝ)^2/Real.pi)|/(2057/2)^3)
    (by norm_num : (0:ℝ) ≤ (2379730689/197810890750000 : ℝ))
  have hh := hsq.mpr hc
  norm_num only [KsIndex.AlphaRemarkTrial.compensatedTailEnergy, Nat.cast_ofNat] at ⊢
  norm_num at hh ⊢
  nlinarith

theorem anchorEnergy_b14 :
    KsIndex.AlphaRemarkTrial.compensatedTailEnergy (2161809/5000000 : ℝ) 14 (2*(12387581/10000000 : ℝ)^2/Real.pi) (1+(12387581/10000000 : ℝ)^2) 1023 ≤ (1/5000 : ℝ)^2 := by
  have hg := anchorGroup_b14_abs
  have hd := anchorCorrection_b14_abs
  have hc : |compensatedPowerArcGroup (2161809/5000000 : ℝ) 14 (2*(12387581/10000000 : ℝ)^2/Real.pi) (1+(12387581/10000000 : ℝ)^2) 1024| +
      11*|stieltjesCorrectionD (2161809/5000000 : ℝ) 14 (2*(12387581/10000000 : ℝ)^2/Real.pi)|/(2057/2)^3 ≤ (1991243563/39562178150000000 : ℝ) := by
    norm_num at hg hd ⊢
    linarith
  have hsq := sq_le_sq₀ (by positivity : (0:ℝ) ≤
    |compensatedPowerArcGroup (2161809/5000000 : ℝ) 14 (2*(12387581/10000000 : ℝ)^2/Real.pi) (1+(12387581/10000000 : ℝ)^2) 1024| +
      11*|stieltjesCorrectionD (2161809/5000000 : ℝ) 14 (2*(12387581/10000000 : ℝ)^2/Real.pi)|/(2057/2)^3)
    (by norm_num : (0:ℝ) ≤ (1991243563/39562178150000000 : ℝ))
  have hh := hsq.mpr hc
  norm_num only [KsIndex.AlphaRemarkTrial.compensatedTailEnergy, Nat.cast_ofNat] at ⊢
  norm_num at hh ⊢
  nlinarith

theorem anchorEnergy_c15 :
    KsIndex.AlphaRemarkTrial.compensatedTailEnergy (2838191/5000000 : ℝ) 15 (2*(12387581/10000000 : ℝ)^2/Real.pi) (1+(12387581/10000000 : ℝ)^2) 1023 ≤ (1/5000 : ℝ)^2 := by
  have hg := anchorGroup_c15_abs
  have hd := anchorCorrection_c15_abs
  have hc : |compensatedPowerArcGroup (2838191/5000000 : ℝ) 15 (2*(12387581/10000000 : ℝ)^2/Real.pi) (1+(12387581/10000000 : ℝ)^2) 1024| +
      11*|stieltjesCorrectionD (2838191/5000000 : ℝ) 15 (2*(12387581/10000000 : ℝ)^2/Real.pi)|/(2057/2)^3 ≤ (1991243563/39562178150000000 : ℝ) := by
    norm_num at hg hd ⊢
    linarith
  have hsq := sq_le_sq₀ (by positivity : (0:ℝ) ≤
    |compensatedPowerArcGroup (2838191/5000000 : ℝ) 15 (2*(12387581/10000000 : ℝ)^2/Real.pi) (1+(12387581/10000000 : ℝ)^2) 1024| +
      11*|stieltjesCorrectionD (2838191/5000000 : ℝ) 15 (2*(12387581/10000000 : ℝ)^2/Real.pi)|/(2057/2)^3)
    (by norm_num : (0:ℝ) ≤ (1991243563/39562178150000000 : ℝ))
  have hh := hsq.mpr hc
  norm_num only [KsIndex.AlphaRemarkTrial.compensatedTailEnergy, Nat.cast_ofNat] at ⊢
  norm_num at hh ⊢
  nlinarith

theorem anchorEnergy_c14 :
    KsIndex.AlphaRemarkTrial.compensatedTailEnergy (2838191/5000000 : ℝ) 14 (2*(12387581/10000000 : ℝ)^2/Real.pi) (1+(12387581/10000000 : ℝ)^2) 1023 ≤ (3/100 : ℝ)^2 := by
  have hg := anchorGroup_c14_abs
  have hd := anchorCorrection_c14_abs
  have hc : |compensatedPowerArcGroup (2838191/5000000 : ℝ) 14 (2*(12387581/10000000 : ℝ)^2/Real.pi) (1+(12387581/10000000 : ℝ)^2) 1024| +
      11*|stieltjesCorrectionD (2838191/5000000 : ℝ) 14 (2*(12387581/10000000 : ℝ)^2/Real.pi)|/(2057/2)^3 ≤ (796043563/158248712600000 : ℝ) := by
    norm_num at hg hd ⊢
    linarith
  have hsq := sq_le_sq₀ (by positivity : (0:ℝ) ≤
    |compensatedPowerArcGroup (2838191/5000000 : ℝ) 14 (2*(12387581/10000000 : ℝ)^2/Real.pi) (1+(12387581/10000000 : ℝ)^2) 1024| +
      11*|stieltjesCorrectionD (2838191/5000000 : ℝ) 14 (2*(12387581/10000000 : ℝ)^2/Real.pi)|/(2057/2)^3)
    (by norm_num : (0:ℝ) ≤ (796043563/158248712600000 : ℝ))
  have hh := hsq.mpr hc
  norm_num only [KsIndex.AlphaRemarkTrial.compensatedTailEnergy, Nat.cast_ofNat] at ⊢
  norm_num at hh ⊢
  nlinarith

end KsIndex.PowerArc

namespace KsIndex.AlphaRemarkTrial
open PowerArc

/-- Certified square-root energy bounds for the four groups. -/
noncomputable def anchorGroupU : Fin 4 → ℝ := ![1/20, 1/5000, 1/5000, 3/100]

theorem anchorGroupU_pos (i : Fin 4) : 0 < anchorGroupU i := by
  fin_cases i <;> norm_num [anchorGroupU]

theorem anchorGroupEnergy_bound (i : Fin 4) :
    compensatedTailEnergy (tailGroupExponent i) (tailGroupEndpoint i)
      (2*AlphaRemark.spectralUpper^2/Real.pi) (1+AlphaRemark.spectralUpper^2) 1023 ≤
      anchorGroupU i^2 := by
  fin_cases i
  · convert anchorEnergy_b15 using 1 <;>
      norm_num [tailGroupExponent, tailGroupEndpoint, anchorGroupU, AlphaRemark.spectralUpper]
  · convert anchorEnergy_b14 using 1 <;>
      norm_num [tailGroupExponent, tailGroupEndpoint, anchorGroupU, AlphaRemark.spectralUpper]
  · convert anchorEnergy_c15 using 1 <;>
      norm_num [tailGroupExponent, tailGroupEndpoint, anchorGroupU, AlphaRemark.spectralUpper]
  · convert anchorEnergy_c14 using 1 <;>
      norm_num [tailGroupExponent, tailGroupEndpoint, anchorGroupU, AlphaRemark.spectralUpper]

end KsIndex.AlphaRemarkTrial
