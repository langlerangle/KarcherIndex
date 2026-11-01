module

public import KsIndexLean.AlphaResidualDefectAlgebra

@[expose] public section


/-! Bounds for an inhomogeneous recurrence using a decaying correction.

A correction whose decrease dominates the forcing gives a bound by a solution
of the homogeneous recurrence. The cubic correction is suited to the
twice-compensated power-arc Stieltjes recurrence.
-/

namespace KsIndex.AlphaResidual

/-- Absorb the forcing into a correction and propagate the initial bound. -/
theorem recurrence_bound_with_correction
    (f q e p h : ℕ → ℝ) (C K : ℝ)
    (hq : ∀ n, 0 ≤ q n)
    (hf : ∀ n, f (n + 1) = q n * f n + e n)
    (hp : ∀ n, p (n + 1) = q n * p n)
    (he : ∀ n, |e n| ≤ K * (q n * h n - h (n + 1)))
    (hzero : |f 0| + K * h 0 ≤ C * p 0) :
    ∀ n, |f n| + K * h n ≤ C * p n := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    have hmul := mul_le_mul_of_nonneg_left ih (hq n)
    have habs : |f (n + 1)| ≤ q n * |f n| + |e n| := by
      rw [hf n]
      calc
        |q n * f n + e n| ≤ |q n * f n| + |e n| := abs_add_le _ _
        _ = q n * |f n| + |e n| := by rw [abs_mul, abs_of_nonneg (hq n)]
    rw [hp n]
    nlinarith [he n]

/-- A nonnegative correction can be discarded after recurrence comparison. -/
theorem recurrence_abs_bound
    (f q e p h : ℕ → ℝ) (C K : ℝ)
    (hq : ∀ n, 0 ≤ q n) (hK : 0 ≤ K) (hh : ∀ n, 0 ≤ h n)
    (hf : ∀ n, f (n + 1) = q n * f n + e n)
    (hp : ∀ n, p (n + 1) = q n * p n)
    (he : ∀ n, |e n| ≤ K * (q n * h n - h (n + 1)))
    (hzero : |f 0| + K * h 0 ≤ C * p 0) :
    ∀ n, |f n| ≤ C * p n := by
  intro n
  have hb := recurrence_bound_with_correction f q e p h C K hq hf hp he hzero n
  have hn := mul_nonneg hK (hh n)
  linarith

/-- Exact decrease of a reciprocal-cubic correction. -/
theorem cubic_correction_difference (A B z : ℝ)
    (hz : z ≠ 0) (hz1 : z + 1 ≠ 0) (hd : z + 1 - A ≠ 0) :
    (z + 1 - B) / (z + 1 - A) / z ^ 3 - 1 / (z + 1) ^ 3 =
      ((A - B + 3) * z ^ 3 + (6 - 3 * B) * z ^ 2 +
        (4 - 3 * B) * z + 1 - B) /
        (z ^ 3 * (z + 1) ^ 3 * (z + 1 - A)) := by
  field_simp
  ring

/-- A polynomial inequality suffices to dominate the compensated forcing by
the decrease of the cubic correction. -/
theorem cubic_forcing_bound (A B z D K : ℝ)
    (hz : 0 < z) (hd : 0 < z + 1 - A)
    (hpoly : |D| * |(A + B - 1) * z + B - 1| * z * (z + 1) ≤
      K * ((A - B + 3) * z ^ 3 + (6 - 3 * B) * z ^ 2 +
        (4 - 3 * B) * z + 1 - B)) :
    |D * ((A + B - 1) * z + B - 1) /
        (z ^ 2 * (z + 1) ^ 2 * (z + 1 - A))| ≤
      K * ((z + 1 - B) / (z + 1 - A) / z ^ 3 - 1 / (z + 1) ^ 3) := by
  have hz1 : 0 < z + 1 := by linarith
  have hden : 0 < z ^ 3 * (z + 1) ^ 3 * (z + 1 - A) := by positivity
  rw [cubic_correction_difference A B z (ne_of_gt hz) (ne_of_gt hz1) (ne_of_gt hd)]
  rw [abs_div, abs_mul, abs_of_pos (by positivity :
    0 < z ^ 2 * (z + 1) ^ 2 * (z + 1 - A))]
  have hid : |D| * |(A + B - 1) * z + B - 1| /
      (z ^ 2 * (z + 1) ^ 2 * (z + 1 - A)) =
      (|D| * |(A + B - 1) * z + B - 1| * z * (z + 1)) /
        (z ^ 3 * (z + 1) ^ 3 * (z + 1 - A)) := by
    field_simp
  rw [hid, ← mul_div_assoc]
  exact (div_le_div_iff_of_pos_right hden).2 hpoly

end KsIndex.AlphaResidual
