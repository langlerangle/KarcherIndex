module

public import KsIndexLean.AlphaStieltjesSeedB14
public import KsIndexLean.AlphaStieltjesSeedB15
public import KsIndexLean.AlphaStieltjesSeedC14
public import KsIndexLean.AlphaStieltjesSeedC15

@[expose] public section


/-! Certified finite normalized Stieltjes sums at the outer-tail seed coordinate. -/
namespace KsIndex.PowerArc

noncomputable def stieltjesSeedPrefix (B r : ℤ) : ℝ :=
  ∑ k ∈ Finset.range 32768, (-1 : ℝ) ^ k *
    normalizedCoefficient ((B : ℝ) / 5000000) r k / ((k : ℝ) + 2057 / 2)

theorem stieltjesSeedPrefix_error (B r : ℤ) (hB : 0 < B) (hr : 0 ≤ r) :
    |stieltjesSeedPrefix B r -
      ((roundedStieltjesState B 5000000 r 1000000000000000000000000000000 2057 2 32768).2 : ℝ) / 1000000000000000000000000000000| ≤
      2 / (10^24) := by
  have hh := roundedStieltjesState_error B 5000000 r 1000000000000000000000000000000 2057 2 32768
    hB (by norm_num) hr (by norm_num) (by norm_num) (by norm_num)
  norm_num only [Int.cast_ofNat, Nat.cast_ofNat] at hh
  apply hh.trans
  norm_num

theorem stieltjesSeedPrefix_b14_error :
    |stieltjesSeedPrefix 2161809 14 - (13863488943026704403213801411 : ℝ) / 1000000000000000000000000000000| ≤ 2 / (10^24) := by
  have hh := stieltjesSeedPrefix_error 2161809 14 (by norm_num) (by norm_num)
  rw [StieltjesSeed2161809R14N32768.state_32768] at hh
  simpa only [Prod.snd, Int.cast_ofNat] using hh

theorem stieltjesSeedPrefix_b15_error :
    |stieltjesSeedPrefix 2161809 15 - (14748424018608785814253409991 : ℝ) / 1000000000000000000000000000000| ≤ 2 / (10^24) := by
  have hh := stieltjesSeedPrefix_error 2161809 15 (by norm_num) (by norm_num)
  rw [StieltjesSeed2161809R15N32768.state_32768] at hh
  simpa only [Prod.snd, Int.cast_ofNat] using hh

theorem stieltjesSeedPrefix_c14_error :
    |stieltjesSeedPrefix 2838191 14 - (11366400885265198921139809997 : ℝ) / 1000000000000000000000000000000| ≤ 2 / (10^24) := by
  have hh := stieltjesSeedPrefix_error 2838191 14 (by norm_num) (by norm_num)
  rw [StieltjesSeed2838191R14N32768.state_32768] at hh
  simpa only [Prod.snd, Int.cast_ofNat] using hh

theorem stieltjesSeedPrefix_c15_error :
    |stieltjesSeedPrefix 2838191 15 - (12101209015989524492755234397 : ℝ) / 1000000000000000000000000000000| ≤ 2 / (10^24) := by
  have hh := stieltjesSeedPrefix_error 2838191 15 (by norm_num) (by norm_num)
  rw [StieltjesSeed2838191R15N32768.state_32768] at hh
  simpa only [Prod.snd, Int.cast_ofNat] using hh

/-- The retained next coefficient also has an explicit recurrence error. -/
theorem stieltjesSeedEndpoint_error (B r : ℤ) (hB : 0 < B) (hr : 0 ≤ r) :
    |normalizedCoefficient ((B : ℝ) / 5000000) r 32768 -
      ((roundedStieltjesState B 5000000 r 1000000000000000000000000000000 2057 2 32768).1 : ℝ) /
        1000000000000000000000000000000| ≤ 32768 / 1000000000000000000000000000000 := by
  rw [roundedStieltjesState_fst]
  have hh := roundedCoefficient_error (B := B) (D := 5000000) (r := r)
    (S := 1000000000000000000000000000000) hB (by norm_num) hr (by norm_num) 32768
  norm_num only [Int.cast_ofNat, Nat.cast_ofNat] at hh
  apply hh.trans
  norm_num

theorem stieltjesSeedEndpoint_b14_error :
    |normalizedCoefficient (2161809 / 5000000 : ℝ) 14 32768 -
      (5521272979134826439108065 : ℝ) / 1000000000000000000000000000000| ≤
        32768 / 1000000000000000000000000000000 := by
  have hh := stieltjesSeedEndpoint_error 2161809 14 (by norm_num) (by norm_num)
  rw [StieltjesSeed2161809R14N32768.state_32768] at hh
  simpa only [Prod.fst, Int.cast_ofNat] using hh

theorem stieltjesSeedEndpoint_b15_error :
    |normalizedCoefficient (2161809 / 5000000 : ℝ) 15 32768 -
      (6095643370439698259701659 : ℝ) / 1000000000000000000000000000000| ≤
        32768 / 1000000000000000000000000000000 := by
  have hh := stieltjesSeedEndpoint_error 2161809 15 (by norm_num) (by norm_num)
  rw [StieltjesSeed2161809R15N32768.state_32768] at hh
  simpa only [Prod.fst, Int.cast_ofNat] using hh

theorem stieltjesSeedEndpoint_c14_error :
    |normalizedCoefficient (2838191 / 5000000 : ℝ) 14 32768 -
      (1758841871412359785175254 : ℝ) / 1000000000000000000000000000000| ≤
        32768 / 1000000000000000000000000000000 := by
  have hh := stieltjesSeedEndpoint_error 2838191 14 (by norm_num) (by norm_num)
  rw [StieltjesSeed2838191R14N32768.state_32768] at hh
  simpa only [Prod.fst, Int.cast_ofNat] using hh

theorem stieltjesSeedEndpoint_c15_error :
    |normalizedCoefficient (2838191 / 5000000 : ℝ) 15 32768 -
      (1960183356628423117153250 : ℝ) / 1000000000000000000000000000000| ≤
        32768 / 1000000000000000000000000000000 := by
  have hh := stieltjesSeedEndpoint_error 2838191 15 (by norm_num) (by norm_num)
  rw [StieltjesSeed2838191R15N32768.state_32768] at hh
  simpa only [Prod.fst, Int.cast_ofNat] using hh

end KsIndex.PowerArc
