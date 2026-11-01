module

public import KsIndexLean.AlphaGroupAnchorBounds

@[expose] public section


/-! Signed enclosures for backward propagation from the shared anchor. -/
namespace KsIndex.PowerArc

private theorem affine_group_center_bound (w κ κ₀ T u u₀ H H₀ a a₀ du dH da dk c R : ℝ)
    (hu : |u-u₀| ≤ du) (hH : |H-H₀| ≤ dH) (ha : |a-a₀| ≤ da)
    (hk : |κ-κ₀| ≤ dk) (hdy : 0 ≤ dH + |T| *da)
    (hbudget : |w| *du + (|κ₀|+dk)*(dH+|T| *da) + dk*|-H₀+T*a₀| +
      |w*u₀+κ₀*(-H₀+T*a₀)-c| ≤ R) : |w*u+κ*(-H+T*a)-c| ≤ R := by
  have hu' : |(w*u-c)-(w*u₀-c)| ≤ |w| *du := by
    rw [show (w*u-c)-(w*u₀-c) = w*(u-u₀) by ring, abs_mul]
    exact mul_le_mul_of_nonneg_left hu (abs_nonneg _)
  have hh := affine_group_abs_bound 1 κ κ₀ T (w*u-c) (w*u₀-c) H H₀ a a₀
    (|w| *du) dH da dk R hu' hH ha hk hdy (by
      convert hbudget using 1; ring_nf)
  convert hh using 1; ring_nf

theorem anchorGroup_b15_error :
    |compensatedPowerArcGroup (2161809/5000000 : ℝ) 15
      (2*(12387581/10000000 : ℝ)^2/Real.pi) (1+(12387581/10000000 : ℝ)^2) 1024 -
      (-2212109/200000000000 : ℝ)| ≤ 11/100000000000 := by
  have hh := affine_group_center_bound
    (1+(12387581/10000000 : ℝ)^2) (2*(12387581/10000000 : ℝ)^2/Real.pi)
    (122113351373/125000000000 : ℝ) (152034409177398034/8653788320979307077 : ℝ)
    (g (2161809/5000000 : ℝ) 2042 / g (2161809/5000000 : ℝ) 0) (4090577/500000000000 : ℝ)
    (powerArcStieltjes (2161809/5000000 : ℝ) 15 (2057/2) / g (2161809/5000000 : ℝ) 0) (-85257617/500000000000 : ℝ)
    (g (2161809/5000000 : ℝ) 15 / g (2161809/5000000 : ℝ) 0) (-5779158047/500000000000 : ℝ)
    (1/1000000000000) (1/10000000000) (1/10000000000) (1/1000000000000) (-2212109/200000000000 : ℝ) (11/100000000000)
    (by simpa only using anchorSample_b2042_error)
    (by simpa only using stieltjes_full_b15_interval)
    (by convert stieltjesInitial_b15_error using 1; norm_num)
    trial_kappa_interval (by norm_num) (by norm_num)
  rw [compensatedPowerArcGroup_seed]
  convert hh using 1; norm_num [neg_div]

theorem anchorCorrection_b15_error :
    |stieltjesCorrectionD (2161809/5000000 : ℝ) 15 (2*(12387581/10000000 : ℝ)^2/Real.pi) -
      (-2585772583/1000000000 : ℝ)| ≤ 3/100000000 := by
  have hh := affine_group_center_bound 0 (2*(12387581/10000000 : ℝ)^2/Real.pi)
    (122113351373/125000000000 : ℝ) (624480731316391/2726945265564 : ℝ) 0 0 0 0
    (g (2161809/5000000 : ℝ) 15 / g (2161809/5000000 : ℝ) 0) (-5779158047/500000000000 : ℝ)
    0 0 (1/10000000000) (1/1000000000000) (-2585772583/1000000000 : ℝ) (3/100000000)
    (by norm_num) (by norm_num)
    (by convert stieltjesInitial_b15_error using 1; norm_num)
    trial_kappa_interval (by norm_num) (by norm_num)
  convert hh using 1
  dsimp [stieltjesCorrectionD, stieltjesCorrectionC]
  congr 1
  ring

theorem anchorGroup_b14_error :
    |compensatedPowerArcGroup (2161809/5000000 : ℝ) 14
      (2*(12387581/10000000 : ℝ)^2/Real.pi) (1+(12387581/10000000 : ℝ)^2) 1024 -
      (-4147/250000000000 : ℝ)| ≤ 11/100000000000 := by
  have hh := affine_group_center_bound
    (1+(12387581/10000000 : ℝ)^2) (2*(12387581/10000000 : ℝ)^2/Real.pi)
    (122113351373/125000000000 : ℝ) (426187433097194102/25961364962937921231 : ℝ)
    (g (2161809/5000000 : ℝ) 2043 / g (2161809/5000000 : ℝ) 0) (-2531841/250000000000 : ℝ)
    (powerArcStieltjes (2161809/5000000 : ℝ) 14 (2057/2) / g (2161809/5000000 : ℝ) 0) (71426451/500000000000 : ℝ)
    (g (2161809/5000000 : ℝ) 14 / g (2161809/5000000 : ℝ) 0) (1287680201/125000000000 : ℝ)
    (1/1000000000000) (1/10000000000) (1/10000000000) (1/1000000000000) (-4147/250000000000 : ℝ) (11/100000000000)
    (by simpa only using anchorSample_b2043_error)
    (by simpa only using stieltjes_full_b14_interval)
    (by convert stieltjesInitial_b14_error using 1; norm_num)
    trial_kappa_interval (by norm_num) (by norm_num)
  rw [compensatedPowerArcGroup_seed]
  convert hh using 1; norm_num [neg_div]

theorem anchorCorrection_b14_error :
    |stieltjesCorrectionD (2161809/5000000 : ℝ) 14 (2*(12387581/10000000 : ℝ)^2/Real.pi) -
      (20073073851/10000000000 : ℝ)| ≤ 3/100000000 := by
  have hh := affine_group_center_bound 0 (2*(12387581/10000000 : ℝ)^2/Real.pi)
    (122113351373/125000000000 : ℝ) (4895326581847519/24542507390076 : ℝ) 0 0 0 0
    (g (2161809/5000000 : ℝ) 14 / g (2161809/5000000 : ℝ) 0) (1287680201/125000000000 : ℝ)
    0 0 (1/10000000000) (1/1000000000000) (20073073851/10000000000 : ℝ) (3/100000000)
    (by norm_num) (by norm_num)
    (by convert stieltjesInitial_b14_error using 1; norm_num)
    trial_kappa_interval (by norm_num) (by norm_num)
  convert hh using 1
  dsimp [stieltjesCorrectionD, stieltjesCorrectionC]
  congr 1
  ring

theorem anchorGroup_c15_error :
    |compensatedPowerArcGroup (2838191/5000000 : ℝ) 15
      (2*(12387581/10000000 : ℝ)^2/Real.pi) (1+(12387581/10000000 : ℝ)^2) 1024 -
      (14963/1000000000000 : ℝ)| ≤ 11/100000000000 := by
  have hh := affine_group_center_bound
    (1+(12387581/10000000 : ℝ)^2) (2*(12387581/10000000 : ℝ)^2/Real.pi)
    (122113351373/125000000000 : ℝ) (351751012572194102/25961364962937921231 : ℝ)
    (g (2838191/5000000 : ℝ) 2042 / g (2838191/5000000 : ℝ) 0) (3849223/1000000000000 : ℝ)
    (powerArcStieltjes (2838191/5000000 : ℝ) 15 (2057/2) / g (2838191/5000000 : ℝ) 0) (-83421663/1000000000000 : ℝ)
    (g (2838191/5000000 : ℝ) 15 / g (2838191/5000000 : ℝ) 0) (-1378592951/200000000000 : ℝ)
    (1/1000000000000) (1/10000000000) (1/10000000000) (1/1000000000000) (14963/1000000000000 : ℝ) (11/100000000000)
    (by simpa only using anchorSample_c2042_error)
    (by simpa only using stieltjes_full_c15_interval)
    (by convert stieltjesInitial_c15_error using 1; norm_num)
    trial_kappa_interval (by norm_num) (by norm_num)
  rw [compensatedPowerArcGroup_seed]
  convert hh using 1; norm_num [neg_div]

theorem anchorCorrection_c15_error :
    |stieltjesCorrectionD (2838191/5000000 : ℝ) 15 (2*(12387581/10000000 : ℝ)^2/Real.pi) -
      (-3852835081/2500000000 : ℝ)| ≤ 3/100000000 := by
  have hh := affine_group_center_bound 0 (2*(12387581/10000000 : ℝ)^2/Real.pi)
    (122113351373/125000000000 : ℝ) (5616944671847519/24542507390076 : ℝ) 0 0 0 0
    (g (2838191/5000000 : ℝ) 15 / g (2838191/5000000 : ℝ) 0) (-1378592951/200000000000 : ℝ)
    0 0 (1/10000000000) (1/1000000000000) (-3852835081/2500000000 : ℝ) (3/100000000)
    (by norm_num) (by norm_num)
    (by convert stieltjesInitial_c15_error using 1; norm_num)
    trial_kappa_interval (by norm_num) (by norm_num)
  convert hh using 1
  dsimp [stieltjesCorrectionD, stieltjesCorrectionC]
  congr 1
  ring

theorem anchorGroup_c14_error :
    |compensatedPowerArcGroup (2838191/5000000 : ℝ) 14
      (2*(12387581/10000000 : ℝ)^2/Real.pi) (1+(12387581/10000000 : ℝ)^2) 1024 -
      (83793/20000000000 : ℝ)| ≤ 11/100000000000 := by
  have hh := affine_group_center_bound
    (1+(12387581/10000000 : ℝ)^2) (2*(12387581/10000000 : ℝ)^2/Real.pi)
    (122113351373/125000000000 : ℝ) (766414468548238/60516002244610539 : ℝ)
    (g (2838191/5000000 : ℝ) 2043 / g (2838191/5000000 : ℝ) 0) (-1552471/500000000000 : ℝ)
    (powerArcStieltjes (2838191/5000000 : ℝ) 14 (2057/2) / g (2838191/5000000 : ℝ) 0) (108177701/1000000000000 : ℝ)
    (g (2838191/5000000 : ℝ) 14 / g (2838191/5000000 : ℝ) 0) (9516400877/1000000000000 : ℝ)
    (1/1000000000000) (1/10000000000) (1/10000000000) (1/1000000000000) (83793/20000000000 : ℝ) (11/100000000000)
    (by simpa only using anchorSample_c2043_error)
    (by simpa only using stieltjes_full_c14_interval)
    (by simpa only using stieltjesInitial_c14_error)
    trial_kappa_interval (by norm_num) (by norm_num)
  rw [compensatedPowerArcGroup_seed]
  convert hh using 1; norm_num [neg_div]

theorem anchorCorrection_c14_error :
    |stieltjesCorrectionD (2838191/5000000 : ℝ) 14 (2*(12387581/10000000 : ℝ)^2/Real.pi) -
      (9265278461/5000000000 : ℝ)| ≤ 3/100000000 := by
  have hh := affine_group_center_bound 0 (2*(12387581/10000000 : ℝ)^2/Real.pi)
    (122113351373/125000000000 : ℝ) (125434478765321/629295061284 : ℝ) 0 0 0 0
    (g (2838191/5000000 : ℝ) 14 / g (2838191/5000000 : ℝ) 0) (9516400877/1000000000000 : ℝ)
    0 0 (1/10000000000) (1/1000000000000) (9265278461/5000000000 : ℝ) (3/100000000)
    (by norm_num) (by norm_num)
    (by simpa only using stieltjesInitial_c14_error)
    trial_kappa_interval (by norm_num) (by norm_num)
  convert hh using 1
  dsimp [stieltjesCorrectionD, stieltjesCorrectionC]
  congr 1
  ring

end KsIndex.PowerArc
