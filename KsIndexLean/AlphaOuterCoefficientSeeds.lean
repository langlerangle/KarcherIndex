module

public import KsIndexLean.AlphaStieltjesSeedPrefixCertificate
public import KsIndexLean.AlphaStieltjesInitialCoefficients
public import KsIndexLean.StieltjesScalarEnclosure

@[expose] public section


/-! Certified power-arc coefficients at frequencies 2042 and 2043. -/
namespace KsIndex.PowerArc
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem coefficient_ratio_enclosure (β r : ℝ) (n : ℕ) (q E a₀ d c R : ℝ)
    (hβ : 0 < β) (hr : 0 ≤ r)
    (hq : |normalizedCoefficient β r n - q| ≤ E)
    (ha : |g β r / g β 0 - a₀| ≤ d) (hE : 0 ≤ E)
    (hbudget : (|a₀| + d) * E + d * |q| + |a₀ * q - c| ≤ R) :
    |g β (r + 2 * n) / g β 0 - c| ≤ R := by
  have hid : g β (r + 2 * n) / g β 0 =
      (g β r / g β 0) * normalizedCoefficient β r n := by
    rw [g_eq_normalizedCoefficient hβ hr]; ring
  have hh : |g β (r + 2 * n) / g β 0 - (g β r / g β 0) * q| ≤
      |g β r / g β 0| * E := by
    rw [hid, ← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left hq (abs_nonneg _)
  exact scalar_enclosure_transfer _ _ a₀ q E d c R hh ha hE hbudget

theorem outer_state_b14 :
    roundedStieltjesState 2161809 5000000 14 1000000000000000000000000000000 2057 2 1014 = (794175688094684303728189264, 13507270432641085020720254929) := by
  rw [show 1014 = 896 + 118 from rfl, roundedStieltjesState_add,
    StieltjesSeed2161809R14N32768.state_896]
  decide

theorem outer_normalized_b14_error :
    |normalizedCoefficient (2161809/5000000 : ℝ) 14 1014 - (794175688094684303728189264 : ℝ)/1000000000000000000000000000000| ≤ 1014/1000000000000000000000000000000 := by
  have hh := roundedCoefficient_error (B := 2161809) (D := 5000000) (r := 14) (S := 1000000000000000000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1014
  have he := congrArg Prod.fst outer_state_b14
  rw [roundedStieltjesState_fst] at he
  rw [he] at hh
  norm_num only [Prod.fst, Int.cast_ofNat, Nat.cast_ofNat] at hh
  norm_num only [Int.cast_ofNat, Nat.cast_ofNat]
  exact hh

theorem outer_coefficient_b14_interval :
    |g (2161809/5000000 : ℝ) 2042 / g (2161809/5000000 : ℝ) 0 - (818115447 : ℝ)/100000000000000| ≤
      1/1000000000000 := by
  have hh := coefficient_ratio_enclosure (2161809/5000000 : ℝ) 14 1014
    (794175688094684303728189264/1000000000000000000000000000000) (1014/1000000000000000000000000000000) (10301441608/1000000000000) (1/10000000000)
    (818115447/100000000000000) (1/1000000000000)
    (by norm_num) (by norm_num) outer_normalized_b14_error
    stieltjesInitial_b14_error (by norm_num) (by norm_num)
  convert! hh using 1; norm_num

theorem outer_state_b15 :
    roundedStieltjesState 2161809 5000000 15 1000000000000000000000000000000 2057 2 1014 = (876197171707867862131988340, 14355290696448169839324405692) := by
  rw [show 1014 = 896 + 118 from rfl, roundedStieltjesState_add,
    StieltjesSeed2161809R15N32768.state_896]
  decide

theorem outer_normalized_b15_error :
    |normalizedCoefficient (2161809/5000000 : ℝ) 15 1014 - (876197171707867862131988340 : ℝ)/1000000000000000000000000000000| ≤ 1014/1000000000000000000000000000000 := by
  have hh := roundedCoefficient_error (B := 2161809) (D := 5000000) (r := 15) (S := 1000000000000000000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1014
  have he := congrArg Prod.fst outer_state_b15
  rw [roundedStieltjesState_fst] at he
  rw [he] at hh
  norm_num only [Prod.fst, Int.cast_ofNat, Nat.cast_ofNat] at hh
  norm_num only [Int.cast_ofNat, Nat.cast_ofNat]
  exact hh

theorem outer_coefficient_b15_interval :
    |g (2161809/5000000 : ℝ) 2043 / g (2161809/5000000 : ℝ) 0 - (-1012736388 : ℝ)/100000000000000| ≤
      1/1000000000000 := by
  have hh := coefficient_ratio_enclosure (2161809/5000000 : ℝ) 15 1014
    (876197171707867862131988340/1000000000000000000000000000000) (1014/1000000000000000000000000000000) (-11558316094/1000000000000) (1/10000000000)
    (-1012736388/100000000000000) (1/1000000000000)
    (by norm_num) (by norm_num) outer_normalized_b15_error
    stieltjesInitial_b15_error (by norm_num) (by norm_num)
  convert! hh using 1; norm_num

theorem outer_state_c14 :
    roundedStieltjesState 2838191 5000000 14 1000000000000000000000000000000 2057 2 1014 = (404483088447845852920718627, 11202582490076045125288367166) := by
  rw [show 1014 = 896 + 118 from rfl, roundedStieltjesState_add,
    StieltjesSeed2838191R14N32768.state_896]
  decide

theorem outer_normalized_c14_error :
    |normalizedCoefficient (2838191/5000000 : ℝ) 14 1014 - (404483088447845852920718627 : ℝ)/1000000000000000000000000000000| ≤ 1014/1000000000000000000000000000000 := by
  have hh := roundedCoefficient_error (B := 2838191) (D := 5000000) (r := 14) (S := 1000000000000000000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1014
  have he := congrArg Prod.fst outer_state_c14
  rw [roundedStieltjesState_fst] at he
  rw [he] at hh
  norm_num only [Prod.fst, Int.cast_ofNat, Nat.cast_ofNat] at hh
  norm_num only [Int.cast_ofNat, Nat.cast_ofNat]
  exact hh

theorem outer_coefficient_c14_interval :
    |g (2838191/5000000 : ℝ) 2042 / g (2838191/5000000 : ℝ) 0 - (384922321 : ℝ)/100000000000000| ≤
      1/1000000000000 := by
  have hh := coefficient_ratio_enclosure (2838191/5000000 : ℝ) 14 1014
    (404483088447845852920718627/1000000000000000000000000000000) (1014/1000000000000000000000000000000) (9516400877/1000000000000) (1/10000000000)
    (384922321/100000000000000) (1/1000000000000)
    (by norm_num) (by norm_num) outer_normalized_c14_error
    stieltjesInitial_c14_error (by norm_num) (by norm_num)
  convert! hh using 1; norm_num

theorem outer_state_c15 :
    roundedStieltjesState 2838191 5000000 15 1000000000000000000000000000000 2057 2 1014 = (450450766960996198791847591, 11918713059537643155980993740) := by
  rw [show 1014 = 896 + 118 from rfl, roundedStieltjesState_add,
    StieltjesSeed2838191R15N32768.state_896]
  decide

theorem outer_normalized_c15_error :
    |normalizedCoefficient (2838191/5000000 : ℝ) 15 1014 - (450450766960996198791847591 : ℝ)/1000000000000000000000000000000| ≤ 1014/1000000000000000000000000000000 := by
  have hh := roundedCoefficient_error (B := 2838191) (D := 5000000) (r := 15) (S := 1000000000000000000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1014
  have he := congrArg Prod.fst outer_state_c15
  rw [roundedStieltjesState_fst] at he
  rw [he] at hh
  norm_num only [Prod.fst, Int.cast_ofNat, Nat.cast_ofNat] at hh
  norm_num only [Int.cast_ofNat, Nat.cast_ofNat]
  exact hh

theorem outer_coefficient_c15_interval :
    |g (2838191/5000000 : ℝ) 2043 / g (2838191/5000000 : ℝ) 0 - (-310494127 : ℝ)/100000000000000| ≤
      1/1000000000000 := by
  have hh := coefficient_ratio_enclosure (2838191/5000000 : ℝ) 15 1014
    (450450766960996198791847591/1000000000000000000000000000000) (1014/1000000000000000000000000000000) (-6892964755/1000000000000) (1/10000000000)
    (-310494127/100000000000000) (1/1000000000000)
    (by norm_num) (by norm_num) outer_normalized_c15_error
    stieltjesInitial_c15_error (by norm_num) (by norm_num)
  convert! hh using 1; norm_num

end KsIndex.PowerArc
