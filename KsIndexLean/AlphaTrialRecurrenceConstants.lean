module

public import KsIndexLean.AlphaResidualRecurrenceBound

@[expose] public section


/-! A rational forcing bound for the four power-arc shift groups of the trial.

The estimate starts at the outer cutoff 1024 (the Stieltjes coordinate is then
1028.5). It bounds the forcing only; initial residual values require separate
certificates.
-/

namespace KsIndex.AlphaResidual

/-- A common rational bound for both exponents and both shift parities. -/
theorem trial_cubic_polynomial_bound (β r z : ℝ)
    (hβ : β = 4323618 / 10000000 ∨ β = 5676382 / 10000000)
    (hr : r = 14 ∨ r = 15) (hz : 1028 ≤ z) :
    (r * z + (r + β) / 2) * z * (z + 1) ≤
      11 * ((2 - β) * z ^ 3 + (6 - 3 * ((r + β + 2) / 2)) * z ^ 2 +
        (4 - 3 * ((r + β + 2) / 2)) * z + 1 - (r + β + 2) / 2) := by
  suffices h : 0 ≤
      11 * ((2 - β) * z ^ 3 + (6 - 3 * ((r + β + 2) / 2)) * z ^ 2 +
        (4 - 3 * ((r + β + 2) / 2)) * z + 1 - (r + β + 2) / 2) -
      (r * z + (r + β) / 2) * z * (z + 1) by linarith
  let y := z - 1028
  have hy : 0 ≤ y := sub_nonneg.mpr hz
  have hz' : z = 1028 + y := by dsimp [y]; ring
  rw [hz']
  rcases hβ with rfl | rfl <;> rcases hr with rfl | rfl
  all_goals
    norm_num
    ring_nf
    nlinarith [sq_nonneg y, pow_nonneg hy 3]

/-- The common cubic correction dominates the forcing with coefficient
`11 * |D|`, uniformly beyond the outer cutoff. -/
theorem trial_cubic_forcing_bound (β r z D : ℝ)
    (hβ : β = 4323618 / 10000000 ∨ β = 5676382 / 10000000)
    (hr : r = 14 ∨ r = 15) (hz : 1028 ≤ z) :
    |D * (r * z + (r + β) / 2) /
        (z ^ 2 * (z + 1) ^ 2 * (z + 1 - (r - β) / 2))| ≤
      (11 * |D|) *
        ((z + 1 - (r + β + 2) / 2) / (z + 1 - (r - β) / 2) / z ^ 3 -
          1 / (z + 1) ^ 3) := by
  have hz0 : 0 < z := by linarith
  have hd : 0 < z + 1 - (r - β) / 2 := by
    rcases hβ with rfl | rfl <;> rcases hr with rfl | rfl <;> norm_num at * <;> linarith
  have hpos : 0 ≤ r * z + (r + β) / 2 := by
    rcases hβ with rfl | rfl <;> rcases hr with rfl | rfl <;> norm_num at * <;> linarith
  have hid : (r - β) / 2 + (r + β + 2) / 2 - 1 = r := by ring
  have hid' : (r - β) / 2 - (r + β + 2) / 2 + 3 = 2 - β := by ring
  have hlin : ((r - β) / 2 + (r + β + 2) / 2 - 1) * z +
      (r + β + 2) / 2 - 1 = r * z + (r + β) / 2 := by rw [hid]; ring
  have hp := mul_le_mul_of_nonneg_left (trial_cubic_polynomial_bound β r z hβ hr hz)
    (abs_nonneg D)
  have hb := cubic_forcing_bound ((r - β) / 2) ((r + β + 2) / 2) z D (11 * |D|)
    hz0 hd
  rw [hlin, hid', abs_of_nonneg hpos] at hb
  apply hb
  nlinarith [hp]

end KsIndex.AlphaResidual
