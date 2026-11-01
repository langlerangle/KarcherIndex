module

public import Mathlib

@[expose] public section


/-! Propagation of a scalar normalization interval through a certified enclosure. -/

namespace KsIndex.PowerArc

theorem scalar_enclosure_transfer (H a a₀ T E d c R : ℝ)
    (hH : |H - a * T| ≤ |a| * E) (ha : |a - a₀| ≤ d) (hE : 0 ≤ E)
    (hbudget : (|a₀| + d) * E + d * |T| + |a₀ * T - c| ≤ R) :
    |H - c| ≤ R := by
  have habs : |a| ≤ |a₀| + d := by
    have hh := abs_sub_le a a₀ 0
    simp only [sub_zero] at hh
    linarith
  have hprod : |a * T - a₀ * T| ≤ d * |T| := by
    rw [← sub_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)
  have hmain : |H - a * T| ≤ (|a₀| + d) * E :=
    hH.trans (mul_le_mul_of_nonneg_right habs hE)
  have hfirst := abs_sub_le H (a * T) (a₀ * T)
  have hsecond := abs_sub_le H (a₀ * T) c
  linarith

end KsIndex.PowerArc
