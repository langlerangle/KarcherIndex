module

public import KsIndexLean.AlphaOuterCoefficientSeeds

@[expose] public section


/-! Normalized coefficient intervals at the energy-tail sampling anchors. -/
namespace KsIndex.PowerArc
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem energy8192_b14_state :
    roundedStieltjesState 2161809 5000000 14 1000000000000000000000000000000 2057 2 8182 = (40250166021245727358167329, 13841069434945282767188700440) := by
  rw [show 8182 = 8064 + 118 from rfl, roundedStieltjesState_add,
    StieltjesSeed2161809R14N32768.state_8064]
  decide

theorem energy8192_b14_normalized :
    |normalizedCoefficient (2161809/5000000 : ℝ) 14 8182 - (40250166021245727358167329 : ℝ)/1000000000000000000000000000000| ≤ 8182/1000000000000000000000000000000 := by
  have hh := roundedCoefficient_error (B := 2161809) (D := 5000000) (r := 14) (S := 1000000000000000000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 8182
  have he := congrArg Prod.fst energy8192_b14_state
  rw [roundedStieltjesState_fst] at he
  rw [he] at hh
  norm_num only [Prod.fst, Int.cast_ofNat, Nat.cast_ofNat] at hh
  norm_num only [Int.cast_ofNat, Nat.cast_ofNat]
  exact hh

theorem energy8192_b14_interval :
    |g (2161809/5000000 : ℝ) 16378/g (2161809/5000000 : ℝ) 0 - (4146347349 : ℝ)/10000000000000000| ≤ 1/100000000000000 := by
  have hh := coefficient_ratio_enclosure (2161809/5000000 : ℝ) 14 8182
    (40250166021245727358167329/1000000000000000000000000000000) (8182/1000000000000000000000000000000) (10301441608/1000000000000) (1/10000000000)
    (4146347349/10000000000000000) (1/100000000000000)
    (by norm_num) (by norm_num) energy8192_b14_normalized
    stieltjesInitial_b14_error (by norm_num) (by norm_num)
  convert! hh using 1; norm_num

theorem energy8192_b15_state :
    roundedStieltjesState 2161809 5000000 15 1000000000000000000000000000000 2057 2 8182 = (44434420015471377958756625, 14723673114739692193763454331) := by
  rw [show 8182 = 8064 + 118 from rfl, roundedStieltjesState_add,
    StieltjesSeed2161809R15N32768.state_8064]
  decide

theorem energy8192_b15_normalized :
    |normalizedCoefficient (2161809/5000000 : ℝ) 15 8182 - (44434420015471377958756625 : ℝ)/1000000000000000000000000000000| ≤ 8182/1000000000000000000000000000000 := by
  have hh := roundedCoefficient_error (B := 2161809) (D := 5000000) (r := 15) (S := 1000000000000000000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 8182
  have he := congrArg Prod.fst energy8192_b15_state
  rw [roundedStieltjesState_fst] at he
  rw [he] at hh
  norm_num only [Prod.fst, Int.cast_ofNat, Nat.cast_ofNat] at hh
  norm_num only [Int.cast_ofNat, Nat.cast_ofNat]
  exact hh

theorem energy8192_b15_interval :
    |g (2161809/5000000 : ℝ) 16379/g (2161809/5000000 : ℝ) 0 - (-5135870720 : ℝ)/10000000000000000| ≤ 1/100000000000000 := by
  have hh := coefficient_ratio_enclosure (2161809/5000000 : ℝ) 15 8182
    (44434420015471377958756625/1000000000000000000000000000000) (8182/1000000000000000000000000000000) (-11558316094/1000000000000) (1/10000000000)
    (-5135870720/10000000000000000) (1/100000000000000)
    (by norm_num) (by norm_num) energy8192_b15_normalized
    stieltjesInitial_b15_error (by norm_num) (by norm_num)
  convert! hh using 1; norm_num

theorem energy8192_c14_state :
    roundedStieltjesState 2838191 5000000 14 1000000000000000000000000000000 2057 2 8182 = (15467988068818294995837337, 11358324057772346444974324502) := by
  rw [show 8182 = 8064 + 118 from rfl, roundedStieltjesState_add,
    StieltjesSeed2838191R14N32768.state_8064]
  decide

theorem energy8192_c14_normalized :
    |normalizedCoefficient (2838191/5000000 : ℝ) 14 8182 - (15467988068818294995837337 : ℝ)/1000000000000000000000000000000| ≤ 8182/1000000000000000000000000000000 := by
  have hh := roundedCoefficient_error (B := 2838191) (D := 5000000) (r := 14) (S := 1000000000000000000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 8182
  have he := congrArg Prod.fst energy8192_c14_state
  rw [roundedStieltjesState_fst] at he
  rw [he] at hh
  norm_num only [Prod.fst, Int.cast_ofNat, Nat.cast_ofNat] at hh
  norm_num only [Int.cast_ofNat, Nat.cast_ofNat]
  exact hh

theorem energy8192_c14_interval :
    |g (2838191/5000000 : ℝ) 16378/g (2838191/5000000 : ℝ) 0 - (1471995752 : ℝ)/10000000000000000| ≤ 1/100000000000000 := by
  have hh := coefficient_ratio_enclosure (2838191/5000000 : ℝ) 14 8182
    (15467988068818294995837337/1000000000000000000000000000000) (8182/1000000000000000000000000000000) (9516400877/1000000000000) (1/10000000000)
    (1471995752/10000000000000000) (1/100000000000000)
    (by norm_num) (by norm_num) energy8192_c14_normalized
    stieltjesInitial_c14_error (by norm_num) (by norm_num)
  convert! hh using 1; norm_num

theorem energy8192_c15_state :
    roundedStieltjesState 2838191 5000000 15 1000000000000000000000000000000 2057 2 8182 = (17237431298263067314776605, 12092207959539848163554230287) := by
  rw [show 8182 = 8064 + 118 from rfl, roundedStieltjesState_add,
    StieltjesSeed2838191R15N32768.state_8064]
  decide

theorem energy8192_c15_normalized :
    |normalizedCoefficient (2838191/5000000 : ℝ) 15 8182 - (17237431298263067314776605 : ℝ)/1000000000000000000000000000000| ≤ 8182/1000000000000000000000000000000 := by
  have hh := roundedCoefficient_error (B := 2838191) (D := 5000000) (r := 15) (S := 1000000000000000000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 8182
  have he := congrArg Prod.fst energy8192_c15_state
  rw [roundedStieltjesState_fst] at he
  rw [he] at hh
  norm_num only [Prod.fst, Int.cast_ofNat, Nat.cast_ofNat] at hh
  norm_num only [Int.cast_ofNat, Nat.cast_ofNat]
  exact hh

theorem energy8192_c15_interval :
    |g (2838191/5000000 : ℝ) 16379/g (2838191/5000000 : ℝ) 0 - (-1188170065 : ℝ)/10000000000000000| ≤ 1/100000000000000 := by
  have hh := coefficient_ratio_enclosure (2838191/5000000 : ℝ) 15 8182
    (17237431298263067314776605/1000000000000000000000000000000) (8182/1000000000000000000000000000000) (-6892964755/1000000000000) (1/10000000000)
    (-1188170065/10000000000000000) (1/100000000000000)
    (by norm_num) (by norm_num) energy8192_c15_normalized
    stieltjesInitial_c15_error (by norm_num) (by norm_num)
  convert! hh using 1; norm_num

end KsIndex.PowerArc
