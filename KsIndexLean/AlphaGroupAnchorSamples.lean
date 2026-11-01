module

public import KsIndexLean.PowerArcIntegerSamples
public import KsIndexLean.AlphaSeedApproximation

@[expose] public section


/-! Certified integer-frequency samples for the compensated-group energy anchor. -/
namespace KsIndex.PowerArc

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

private theorem coefficient_b2042 :
    roundedCoefficient 2161809 5000000 0 1000000000000000000000000000000 1021 = 8181154478189014699220352 := by decide

theorem anchorSample_b2042_error :
    |g (2161809 / 5000000 : ℝ) 2042 / g (2161809 / 5000000 : ℝ) 0 -
      (4090577 : ℝ) / 500000000000| ≤ 1 / 1000000000000 := by
  have hh := integerSample_bound (B := 2161809) (D := 5000000) (S := 1000000000000000000000000000000)
    (by norm_num) (by norm_num) (by norm_num) gamma_seed_approximation 2042
  norm_num only [Int.cast_ofNat] at hh
  have he : integerSampleError 2161809 5000000 1000000000000000000000000000000
      (719689657/1000000000) (3/1000000000) 2042 +
      |integerSampleCenter 2161809 5000000 1000000000000000000000000000000
        (719689657/1000000000) 2042 - (4090577 : ℝ)/500000000000| ≤ 1/1000000000000 := by
    norm_num [integerSampleError, integerSampleCenter, coefficient_b2042]
  calc
    _ ≤ |g (2161809 / 5000000 : ℝ) 2042 / g (2161809 / 5000000 : ℝ) 0 -
          integerSampleCenter 2161809 5000000 1000000000000000000000000000000 (719689657/1000000000) 2042| +
        |integerSampleCenter 2161809 5000000 1000000000000000000000000000000
          (719689657/1000000000) 2042 - (4090577 : ℝ)/500000000000| := abs_sub_le _ _ _
    _ ≤ _ := (add_le_add hh le_rfl).trans he

private theorem coefficient_b2043 :
    roundedCoefficient 2161809 5000000 1 1000000000000000000000000000000 1021 = -14071848570256196894624137 := by decide

theorem anchorSample_b2043_error :
    |g (2161809 / 5000000 : ℝ) 2043 / g (2161809 / 5000000 : ℝ) 0 -
      (-2531841 : ℝ) / 250000000000| ≤ 1 / 1000000000000 := by
  have hh := integerSample_bound (B := 2161809) (D := 5000000) (S := 1000000000000000000000000000000)
    (by norm_num) (by norm_num) (by norm_num) gamma_seed_approximation 2043
  norm_num only [Int.cast_ofNat] at hh
  have he : integerSampleError 2161809 5000000 1000000000000000000000000000000
      (719689657/1000000000) (3/1000000000) 2043 +
      |integerSampleCenter 2161809 5000000 1000000000000000000000000000000
        (719689657/1000000000) 2043 - (-2531841 : ℝ)/250000000000| ≤ 1/1000000000000 := by
    norm_num [integerSampleError, integerSampleCenter, coefficient_b2043]
  calc
    _ ≤ |g (2161809 / 5000000 : ℝ) 2043 / g (2161809 / 5000000 : ℝ) 0 -
          integerSampleCenter 2161809 5000000 1000000000000000000000000000000 (719689657/1000000000) 2043| +
        |integerSampleCenter 2161809 5000000 1000000000000000000000000000000
          (719689657/1000000000) 2043 - (-2531841 : ℝ)/250000000000| := abs_sub_le _ _ _
    _ ≤ _ := (add_le_add hh le_rfl).trans he

private theorem coefficient_c2042 :
    roundedCoefficient 2838191 5000000 0 1000000000000000000000000000000 1021 = 3849223217859279268112291 := by decide

theorem anchorSample_c2042_error :
    |g (2838191 / 5000000 : ℝ) 2042 / g (2838191 / 5000000 : ℝ) 0 -
      (3849223 : ℝ) / 1000000000000| ≤ 1 / 1000000000000 := by
  have hh := integerSample_bound (B := 2838191) (D := 5000000) (S := 1000000000000000000000000000000)
    (by norm_num) (by norm_num) (by norm_num) beta_seed_approximation 2042
  norm_num only [Int.cast_ofNat] at hh
  have he : integerSampleError 2838191 5000000 1000000000000000000000000000000
      (738631771/1000000000) (1/500000000) 2042 +
      |integerSampleCenter 2838191 5000000 1000000000000000000000000000000
        (738631771/1000000000) 2042 - (3849223 : ℝ)/1000000000000| ≤ 1/1000000000000 := by
    norm_num [integerSampleError, integerSampleCenter, coefficient_c2042]
  calc
    _ ≤ |g (2838191 / 5000000 : ℝ) 2042 / g (2838191 / 5000000 : ℝ) 0 -
          integerSampleCenter 2838191 5000000 1000000000000000000000000000000 (738631771/1000000000) 2042| +
        |integerSampleCenter 2838191 5000000 1000000000000000000000000000000
          (738631771/1000000000) 2042 - (3849223 : ℝ)/1000000000000| := abs_sub_le _ _ _
    _ ≤ _ := (add_le_add hh le_rfl).trans he

private theorem coefficient_c2043 :
    roundedCoefficient 2838191 5000000 1 1000000000000000000000000000000 1021 = -4203638920304295374566062 := by decide

theorem anchorSample_c2043_error :
    |g (2838191 / 5000000 : ℝ) 2043 / g (2838191 / 5000000 : ℝ) 0 -
      (-1552471 : ℝ) / 500000000000| ≤ 1 / 1000000000000 := by
  have hh := integerSample_bound (B := 2838191) (D := 5000000) (S := 1000000000000000000000000000000)
    (by norm_num) (by norm_num) (by norm_num) beta_seed_approximation 2043
  norm_num only [Int.cast_ofNat] at hh
  have he : integerSampleError 2838191 5000000 1000000000000000000000000000000
      (738631771/1000000000) (1/500000000) 2043 +
      |integerSampleCenter 2838191 5000000 1000000000000000000000000000000
        (738631771/1000000000) 2043 - (-1552471 : ℝ)/500000000000| ≤ 1/1000000000000 := by
    norm_num [integerSampleError, integerSampleCenter, coefficient_c2043]
  calc
    _ ≤ |g (2838191 / 5000000 : ℝ) 2043 / g (2838191 / 5000000 : ℝ) 0 -
          integerSampleCenter 2838191 5000000 1000000000000000000000000000000 (738631771/1000000000) 2043| +
        |integerSampleCenter 2838191 5000000 1000000000000000000000000000000
          (738631771/1000000000) 2043 - (-1552471 : ℝ)/500000000000| := abs_sub_le _ _ _
    _ ≤ _ := (add_le_add hh le_rfl).trans he

end KsIndex.PowerArc
