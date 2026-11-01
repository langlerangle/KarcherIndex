module

public import KsIndexLean.AlphaSeedIntervals

@[expose] public section


/-! Rational centers and absolute errors for the positive power-arc seed ratios. -/

namespace KsIndex.PowerArc

theorem gamma_seed_approximation :
    |g (2161809/5000000 : ℝ) 1 / g (2161809/5000000 : ℝ) 0 -
      719689657/1000000000| ≤ 3/1000000000 := by
  have hh := gamma_seed_ratio_bounds
  have hp : 0 < g (2161809/5000000 : ℝ) 1 / g (2161809/5000000 : ℝ) 0 :=
    div_pos (g_pos_of_mem_unit (by norm_num) (by norm_num) (by norm_num))
      (g_pos_of_mem_unit (by norm_num) (by norm_num) (by norm_num))
  apply abs_le.mpr
  constructor <;> nlinarith [hh.1, hh.2]

theorem beta_seed_approximation :
    |g (2838191/5000000 : ℝ) 1 / g (2838191/5000000 : ℝ) 0 -
      738631771/1000000000| ≤ 2/1000000000 := by
  have hh := beta_seed_ratio_bounds
  have hp : 0 < g (2838191/5000000 : ℝ) 1 / g (2838191/5000000 : ℝ) 0 :=
    div_pos (g_pos_of_mem_unit (by norm_num) (by norm_num) (by norm_num))
      (g_pos_of_mem_unit (by norm_num) (by norm_num) (by norm_num))
  apply abs_le.mpr
  constructor <;> nlinarith [hh.1, hh.2]

end KsIndex.PowerArc
