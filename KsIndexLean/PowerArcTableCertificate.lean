module

public import KsIndexLean.PowerArcRounding

@[expose] public section


/-! Finite recurrence tables can be checked locally, without repeatedly
evaluating the recursive coefficient definition at every sample. -/

namespace KsIndex.PowerArc

/-- Local initial-value and recurrence checks identify every entry in a
finite prefix with the rounded coefficient sequence. -/
theorem roundedCoefficient_eq_of_table {B D r S : ℤ} {N : ℕ}
    (t : ℕ → ℤ) (hzero : t 0 = S)
    (hstep : ∀ n < N, t (n + 1) =
      (B - D * (r + 2 * n)) * t n / (B + D * (r + 2 * n + 2)))
    (n : ℕ) (hn : n ≤ N) : t n = roundedCoefficient B D r S n := by
  induction n with
  | zero => simpa only [roundedCoefficient] using hzero
  | succ n ih =>
    rw [hstep n (by omega), roundedCoefficient, ih (by omega)]

/-- A locally verified finite table inherits the analytic rounding bound. -/
theorem normalizedCoefficient_error_of_table {B D r S : ℤ} {N : ℕ}
    (hB : 0 < B) (hD : 0 < D) (hr : 0 ≤ r) (hS : 0 < S)
    (t : ℕ → ℤ) (hzero : t 0 = S)
    (hstep : ∀ n < N, t (n + 1) =
      (B - D * (r + 2 * n)) * t n / (B + D * (r + 2 * n + 2)))
    (n : ℕ) (hn : n ≤ N) :
    |normalizedCoefficient ((B : ℝ) / D) r n - (t n : ℝ) / S| ≤
      n * (1 / (S : ℝ)) := by
  rw [roundedCoefficient_eq_of_table t hzero hstep n hn]
  exact roundedCoefficient_error hB hD hr hS n

end KsIndex.PowerArc
