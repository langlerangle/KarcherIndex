module

public import KsIndexLean.PowerArcIntegerSamples
public import KsIndexLean.AlphaSeedApproximation

@[expose] public section

/-! Rational enclosures of the initial coefficients for the Stieltjes seed groups. -/
namespace KsIndex.PowerArc
theorem stieltjesInitial_b14_error :
    |g (2161809 / 5000000 : ℝ) 14 / g (2161809 / 5000000 : ℝ) 0 -
      (10301441608 : ℝ) / 1000000000000| ≤ 1 / 10000000000 := by
  have hh := integerSample_bound (B := 2161809) (D := 5000000) (S := 1000000000000000000000000000000)
    (by norm_num) (by norm_num) (by norm_num) gamma_seed_approximation 14
  norm_num only [Int.cast_ofNat] at hh
  have he : integerSampleError 2161809 5000000 1000000000000000000000000000000
      (719689657/1000000000) (3/1000000000) 14 +
      |integerSampleCenter 2161809 5000000 1000000000000000000000000000000
        (719689657/1000000000) 14 - (10301441608 : ℝ)/1000000000000| ≤ 1/10000000000 := by
    norm_num [integerSampleError, integerSampleCenter, roundedCoefficient]
  calc
    _ ≤ |g (2161809 / 5000000 : ℝ) 14 / g (2161809 / 5000000 : ℝ) 0 -
          integerSampleCenter 2161809 5000000 1000000000000000000000000000000 (719689657/1000000000) 14| +
        |integerSampleCenter 2161809 5000000 1000000000000000000000000000000
          (719689657/1000000000) 14 - (10301441608 : ℝ)/1000000000000| := abs_sub_le _ _ _
    _ ≤ _ := (add_le_add hh le_rfl).trans he

theorem stieltjesInitial_b15_error :
    |g (2161809 / 5000000 : ℝ) 15 / g (2161809 / 5000000 : ℝ) 0 -
      (-11558316094 : ℝ) / 1000000000000| ≤ 1 / 10000000000 := by
  have hh := integerSample_bound (B := 2161809) (D := 5000000) (S := 1000000000000000000000000000000)
    (by norm_num) (by norm_num) (by norm_num) gamma_seed_approximation 15
  norm_num only [Int.cast_ofNat] at hh
  have he : integerSampleError 2161809 5000000 1000000000000000000000000000000
      (719689657/1000000000) (3/1000000000) 15 +
      |integerSampleCenter 2161809 5000000 1000000000000000000000000000000
        (719689657/1000000000) 15 - (-11558316094 : ℝ)/1000000000000| ≤ 1/10000000000 := by
    norm_num [integerSampleError, integerSampleCenter, roundedCoefficient]
  calc
    _ ≤ |g (2161809 / 5000000 : ℝ) 15 / g (2161809 / 5000000 : ℝ) 0 -
          integerSampleCenter 2161809 5000000 1000000000000000000000000000000 (719689657/1000000000) 15| +
        |integerSampleCenter 2161809 5000000 1000000000000000000000000000000
          (719689657/1000000000) 15 - (-11558316094 : ℝ)/1000000000000| := abs_sub_le _ _ _
    _ ≤ _ := (add_le_add hh le_rfl).trans he

theorem stieltjesInitial_c14_error :
    |g (2838191 / 5000000 : ℝ) 14 / g (2838191 / 5000000 : ℝ) 0 -
      (9516400877 : ℝ) / 1000000000000| ≤ 1 / 10000000000 := by
  have hh := integerSample_bound (B := 2838191) (D := 5000000) (S := 1000000000000000000000000000000)
    (by norm_num) (by norm_num) (by norm_num) beta_seed_approximation 14
  norm_num only [Int.cast_ofNat] at hh
  have he : integerSampleError 2838191 5000000 1000000000000000000000000000000
      (738631771/1000000000) (1/500000000) 14 +
      |integerSampleCenter 2838191 5000000 1000000000000000000000000000000
        (738631771/1000000000) 14 - (9516400877 : ℝ)/1000000000000| ≤ 1/10000000000 := by
    norm_num [integerSampleError, integerSampleCenter, roundedCoefficient]
  calc
    _ ≤ |g (2838191 / 5000000 : ℝ) 14 / g (2838191 / 5000000 : ℝ) 0 -
          integerSampleCenter 2838191 5000000 1000000000000000000000000000000 (738631771/1000000000) 14| +
        |integerSampleCenter 2838191 5000000 1000000000000000000000000000000
          (738631771/1000000000) 14 - (9516400877 : ℝ)/1000000000000| := abs_sub_le _ _ _
    _ ≤ _ := (add_le_add hh le_rfl).trans he

theorem stieltjesInitial_c15_error :
    |g (2838191 / 5000000 : ℝ) 15 / g (2838191 / 5000000 : ℝ) 0 -
      (-6892964755 : ℝ) / 1000000000000| ≤ 1 / 10000000000 := by
  have hh := integerSample_bound (B := 2838191) (D := 5000000) (S := 1000000000000000000000000000000)
    (by norm_num) (by norm_num) (by norm_num) beta_seed_approximation 15
  norm_num only [Int.cast_ofNat] at hh
  have he : integerSampleError 2838191 5000000 1000000000000000000000000000000
      (738631771/1000000000) (1/500000000) 15 +
      |integerSampleCenter 2838191 5000000 1000000000000000000000000000000
        (738631771/1000000000) 15 - (-6892964755 : ℝ)/1000000000000| ≤ 1/10000000000 := by
    norm_num [integerSampleError, integerSampleCenter, roundedCoefficient]
  calc
    _ ≤ |g (2838191 / 5000000 : ℝ) 15 / g (2838191 / 5000000 : ℝ) 0 -
          integerSampleCenter 2838191 5000000 1000000000000000000000000000000 (738631771/1000000000) 15| +
        |integerSampleCenter 2838191 5000000 1000000000000000000000000000000
          (738631771/1000000000) 15 - (-6892964755 : ℝ)/1000000000000| := abs_sub_le _ _ _
    _ ≤ _ := (add_le_add hh le_rfl).trans he

end KsIndex.PowerArc
