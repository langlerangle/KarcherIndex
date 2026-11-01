module

public import KsIndexLean.AlphaOuterCoefficientSeeds

@[expose] public section


/-! Normalized coefficient intervals at the energy-tail sampling anchors. -/
namespace KsIndex.PowerArc
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem qtail_4092_b14_state :
    roundedStieltjesState 2161809 5000000 14 1000000000000000000000000000000 2057 2 2039 = (-293437321392371521187782347, 13707157570094734954436088402) := by
  rw [show 2039 = 1920 + 119 from rfl, roundedStieltjesState_add,
    StieltjesSeed2161809R14N32768.state_1920]
  decide

theorem qtail_4092_b14_normalized :
    |normalizedCoefficient (2161809/5000000 : ℝ) 14 2039 - (-293437321392371521187782347 : ℝ)/1000000000000000000000000000000| ≤ 2039/1000000000000000000000000000000 := by
  have hh := roundedCoefficient_error (B := 2161809) (D := 5000000) (r := 14) (S := 1000000000000000000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 2039
  have he := congrArg Prod.fst qtail_4092_b14_state
  rw [roundedStieltjesState_fst] at he
  rw [he] at hh
  norm_num only [Prod.fst, Int.cast_ofNat, Nat.cast_ofNat] at hh
  norm_num only [Int.cast_ofNat, Nat.cast_ofNat]
  exact hh

theorem qtail_4092_b14_interval :
    |g (2161809/5000000 : ℝ) 4092/g (2161809/5000000 : ℝ) 0 - (-30228274320 : ℝ)/10000000000000000| ≤ 1/10000000000000 := by
  have hh := coefficient_ratio_enclosure (2161809/5000000 : ℝ) 14 2039
    (-293437321392371521187782347/1000000000000000000000000000000) (2039/1000000000000000000000000000000) (10301441608/1000000000000) (1/10000000000)
    (-30228274320/10000000000000000) (1/10000000000000)
    (by norm_num) (by norm_num) qtail_4092_b14_normalized
    stieltjesInitial_b14_error (by norm_num) (by norm_num)
  convert! hh using 1; norm_num

theorem qtail_4092_b15_state :
    roundedStieltjesState 2161809 5000000 15 1000000000000000000000000000000 2057 2 2039 = (-323856910440922887065292831, 14575860568352243003326986911) := by
  rw [show 2039 = 1920 + 119 from rfl, roundedStieltjesState_add,
    StieltjesSeed2161809R15N32768.state_1920]
  decide

theorem qtail_4092_b15_normalized :
    |normalizedCoefficient (2161809/5000000 : ℝ) 15 2039 - (-323856910440922887065292831 : ℝ)/1000000000000000000000000000000| ≤ 2039/1000000000000000000000000000000 := by
  have hh := roundedCoefficient_error (B := 2161809) (D := 5000000) (r := 15) (S := 1000000000000000000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 2039
  have he := congrArg Prod.fst qtail_4092_b15_state
  rw [roundedStieltjesState_fst] at he
  rw [he] at hh
  norm_num only [Prod.fst, Int.cast_ofNat, Nat.cast_ofNat] at hh
  norm_num only [Int.cast_ofNat, Nat.cast_ofNat]
  exact hh

theorem qtail_4092_b15_interval :
    |g (2161809/5000000 : ℝ) 4093/g (2161809/5000000 : ℝ) 0 - (37432405401 : ℝ)/10000000000000000| ≤ 1/10000000000000 := by
  have hh := coefficient_ratio_enclosure (2161809/5000000 : ℝ) 15 2039
    (-323856910440922887065292831/1000000000000000000000000000000) (2039/1000000000000000000000000000000) (-11558316094/1000000000000) (1/10000000000)
    (37432405401/10000000000000000) (1/10000000000000)
    (by norm_num) (by norm_num) qtail_4092_b15_normalized
    stieltjesInitial_b15_error (by norm_num) (by norm_num)
  convert! hh using 1; norm_num

theorem qtail_4092_c14_state :
    roundedStieltjesState 2838191 5000000 14 1000000000000000000000000000000 2057 2 2039 = (-136038519048611227748575180, 11300285248782768316300319072) := by
  rw [show 2039 = 1920 + 119 from rfl, roundedStieltjesState_add,
    StieltjesSeed2838191R14N32768.state_1920]
  decide

theorem qtail_4092_c14_normalized :
    |normalizedCoefficient (2838191/5000000 : ℝ) 14 2039 - (-136038519048611227748575180 : ℝ)/1000000000000000000000000000000| ≤ 2039/1000000000000000000000000000000 := by
  have hh := roundedCoefficient_error (B := 2838191) (D := 5000000) (r := 14) (S := 1000000000000000000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 2039
  have he := congrArg Prod.fst qtail_4092_c14_state
  rw [roundedStieltjesState_fst] at he
  rw [he] at hh
  norm_num only [Prod.fst, Int.cast_ofNat, Nat.cast_ofNat] at hh
  norm_num only [Int.cast_ofNat, Nat.cast_ofNat]
  exact hh

theorem qtail_4092_c14_interval :
    |g (2838191/5000000 : ℝ) 4092/g (2838191/5000000 : ℝ) 0 - (-12945970820 : ℝ)/10000000000000000| ≤ 1/10000000000000 := by
  have hh := coefficient_ratio_enclosure (2838191/5000000 : ℝ) 14 2039
    (-136038519048611227748575180/1000000000000000000000000000000) (2039/1000000000000000000000000000000) (9516400877/1000000000000) (1/10000000000)
    (-12945970820/10000000000000000) (1/10000000000000)
    (by norm_num) (by norm_num) qtail_4092_c14_normalized
    stieltjesInitial_c14_error (by norm_num) (by norm_num)
  convert! hh using 1; norm_num

theorem qtail_4092_c15_state :
    roundedStieltjesState 2838191 5000000 15 1000000000000000000000000000000 2057 2 2039 = (-151556939212075685581357424, 12027539839076813021989754382) := by
  rw [show 2039 = 1920 + 119 from rfl, roundedStieltjesState_add,
    StieltjesSeed2838191R15N32768.state_1920]
  decide

theorem qtail_4092_c15_normalized :
    |normalizedCoefficient (2838191/5000000 : ℝ) 15 2039 - (-151556939212075685581357424 : ℝ)/1000000000000000000000000000000| ≤ 2039/1000000000000000000000000000000 := by
  have hh := roundedCoefficient_error (B := 2838191) (D := 5000000) (r := 15) (S := 1000000000000000000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 2039
  have he := congrArg Prod.fst qtail_4092_c15_state
  rw [roundedStieltjesState_fst] at he
  rw [he] at hh
  norm_num only [Prod.fst, Int.cast_ofNat, Nat.cast_ofNat] at hh
  norm_num only [Int.cast_ofNat, Nat.cast_ofNat]
  exact hh

theorem qtail_4092_c15_interval :
    |g (2838191/5000000 : ℝ) 4093/g (2838191/5000000 : ℝ) 0 - (10446766403 : ℝ)/10000000000000000| ≤ 1/10000000000000 := by
  have hh := coefficient_ratio_enclosure (2838191/5000000 : ℝ) 15 2039
    (-151556939212075685581357424/1000000000000000000000000000000) (2039/1000000000000000000000000000000) (-6892964755/1000000000000) (1/10000000000)
    (10446766403/10000000000000000) (1/10000000000000)
    (by norm_num) (by norm_num) qtail_4092_c15_normalized
    stieltjesInitial_c15_error (by norm_num) (by norm_num)
  convert! hh using 1; norm_num

theorem qtail_32762_b14_state :
    roundedStieltjesState 2161809 5000000 14 1000000000000000000000000000000 2057 2 16374 = (14909733271166488121647168, 13857230971690606364240666585) := by
  rw [show 16374 = 16256 + 118 from rfl, roundedStieltjesState_add,
    StieltjesSeed2161809R14N32768.state_16256]
  decide

theorem qtail_32762_b14_normalized :
    |normalizedCoefficient (2161809/5000000 : ℝ) 14 16374 - (14909733271166488121647168 : ℝ)/1000000000000000000000000000000| ≤ 16374/1000000000000000000000000000000 := by
  have hh := roundedCoefficient_error (B := 2161809) (D := 5000000) (r := 14) (S := 1000000000000000000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 16374
  have he := congrArg Prod.fst qtail_32762_b14_state
  rw [roundedStieltjesState_fst] at he
  rw [he] at hh
  norm_num only [Prod.fst, Int.cast_ofNat, Nat.cast_ofNat] at hh
  norm_num only [Int.cast_ofNat, Nat.cast_ofNat]
  exact hh

theorem qtail_32762_b14_interval :
    |g (2161809/5000000 : ℝ) 32762/g (2161809/5000000 : ℝ) 0 - (1535917466 : ℝ)/10000000000000000| ≤ 1/100000000000000 := by
  have hh := coefficient_ratio_enclosure (2161809/5000000 : ℝ) 14 16374
    (14909733271166488121647168/1000000000000000000000000000000) (16374/1000000000000000000000000000000) (10301441608/1000000000000) (1/10000000000)
    (1535917466/10000000000000000) (1/100000000000000)
    (by norm_num) (by norm_num) qtail_32762_b14_normalized
    stieltjesInitial_b14_error (by norm_num) (by norm_num)
  convert! hh using 1; norm_num

theorem qtail_32762_b15_state :
    roundedStieltjesState 2161809 5000000 15 1000000000000000000000000000000 2057 2 16374 = (16460412236230805780872120, 14741515118033977408505996030) := by
  rw [show 16374 = 16256 + 118 from rfl, roundedStieltjesState_add,
    StieltjesSeed2161809R15N32768.state_16256]
  decide

theorem qtail_32762_b15_normalized :
    |normalizedCoefficient (2161809/5000000 : ℝ) 15 16374 - (16460412236230805780872120 : ℝ)/1000000000000000000000000000000| ≤ 16374/1000000000000000000000000000000 := by
  have hh := roundedCoefficient_error (B := 2161809) (D := 5000000) (r := 15) (S := 1000000000000000000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 16374
  have he := congrArg Prod.fst qtail_32762_b15_state
  rw [roundedStieltjesState_fst] at he
  rw [he] at hh
  norm_num only [Prod.fst, Int.cast_ofNat, Nat.cast_ofNat] at hh
  norm_num only [Int.cast_ofNat, Nat.cast_ofNat]
  exact hh

theorem qtail_32762_b15_interval :
    |g (2161809/5000000 : ℝ) 32763/g (2161809/5000000 : ℝ) 0 - (-1902546477 : ℝ)/10000000000000000| ≤ 1/100000000000000 := by
  have hh := coefficient_ratio_enclosure (2161809/5000000 : ℝ) 15 16374
    (16460412236230805780872120/1000000000000000000000000000000) (16374/1000000000000000000000000000000) (-11558316094/1000000000000) (1/10000000000)
    (-1902546477/10000000000000000) (1/100000000000000)
    (by norm_num) (by norm_num) qtail_32762_b15_normalized
    stieltjesInitial_b15_error (by norm_num) (by norm_num)
  convert! hh using 1; norm_num

theorem qtail_32762_c14_state :
    roundedStieltjesState 2838191 5000000 14 1000000000000000000000000000000 2057 2 16374 = (5216785882211659034687303, 11364295323551456324807601874) := by
  rw [show 16374 = 16256 + 118 from rfl, roundedStieltjesState_add,
    StieltjesSeed2838191R14N32768.state_16256]
  decide

theorem qtail_32762_c14_normalized :
    |normalizedCoefficient (2838191/5000000 : ℝ) 14 16374 - (5216785882211659034687303 : ℝ)/1000000000000000000000000000000| ≤ 16374/1000000000000000000000000000000 := by
  have hh := roundedCoefficient_error (B := 2838191) (D := 5000000) (r := 14) (S := 1000000000000000000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 16374
  have he := congrArg Prod.fst qtail_32762_c14_state
  rw [roundedStieltjesState_fst] at he
  rw [he] at hh
  norm_num only [Prod.fst, Int.cast_ofNat, Nat.cast_ofNat] at hh
  norm_num only [Int.cast_ofNat, Nat.cast_ofNat]
  exact hh

theorem qtail_32762_c14_interval :
    |g (2838191/5000000 : ℝ) 32762/g (2838191/5000000 : ℝ) 0 - (496450257 : ℝ)/10000000000000000| ≤ 1/100000000000000 := by
  have hh := coefficient_ratio_enclosure (2838191/5000000 : ℝ) 14 16374
    (5216785882211659034687303/1000000000000000000000000000000) (16374/1000000000000000000000000000000) (9516400877/1000000000000) (1/10000000000)
    (496450257/10000000000000000) (1/100000000000000)
    (by norm_num) (by norm_num) qtail_32762_c14_normalized
    stieltjesInitial_c14_error (by norm_num) (by norm_num)
  convert! hh using 1; norm_num

theorem qtail_32762_c15_state :
    roundedStieltjesState 2838191 5000000 15 1000000000000000000000000000000 2057 2 16374 = (5813832550351951492775779, 12098862452157663110371106380) := by
  rw [show 16374 = 16256 + 118 from rfl, roundedStieltjesState_add,
    StieltjesSeed2838191R15N32768.state_16256]
  decide

theorem qtail_32762_c15_normalized :
    |normalizedCoefficient (2838191/5000000 : ℝ) 15 16374 - (5813832550351951492775779 : ℝ)/1000000000000000000000000000000| ≤ 16374/1000000000000000000000000000000 := by
  have hh := roundedCoefficient_error (B := 2838191) (D := 5000000) (r := 15) (S := 1000000000000000000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 16374
  have he := congrArg Prod.fst qtail_32762_c15_state
  rw [roundedStieltjesState_fst] at he
  rw [he] at hh
  norm_num only [Prod.fst, Int.cast_ofNat, Nat.cast_ofNat] at hh
  norm_num only [Int.cast_ofNat, Nat.cast_ofNat]
  exact hh

theorem qtail_32762_c15_interval :
    |g (2838191/5000000 : ℝ) 32763/g (2838191/5000000 : ℝ) 0 - (-400745429 : ℝ)/10000000000000000| ≤ 1/100000000000000 := by
  have hh := coefficient_ratio_enclosure (2838191/5000000 : ℝ) 15 16374
    (5813832550351951492775779/1000000000000000000000000000000) (16374/1000000000000000000000000000000) (-6892964755/1000000000000) (1/10000000000)
    (-400745429/10000000000000000) (1/100000000000000)
    (by norm_num) (by norm_num) qtail_32762_c15_normalized
    stieltjesInitial_c15_error (by norm_num) (by norm_num)
  convert! hh using 1; norm_num

end KsIndex.PowerArc
