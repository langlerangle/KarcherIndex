module

public import KsIndexLean.DecimalPeriodArithmetic
public import KsIndexLean.AlphaRemarkLowerCertified
public import KsIndexLean.NegSignDecimal

@[expose] public section


/-! Explicit floor values and nonresonance through period 2298.
This optional module imports both numerical certificate stacks. -/
namespace KsIndex.Staircase

/-- The exact floor determined by the certified interval, for positive periods at most 2298. -/
theorem alphaStar_floor_le_2298 {m : ℕ} (hm : 0 < m) (hbound : m ≤ 2298) :
    ⌊(m : ℝ) * alphaStar⌋₊ = 4323617 * m / 10000000 :=
  DecimalPeriodArithmetic.decimal_floor
    AlphaRemarkTrial.LowerAssembly.alphaStar_gt_4323617
    NegSignProd.alphaStar_lt_upper_decimal hm hbound

/-- No exceptional bounded-field nullity occurs through period 2298. -/
theorem alphaStar_nonresonant_le_2298 {m : ℕ} (hm : 0 < m) (hbound : m ≤ 2298) :
    ¬ ∃ z : ℤ, (m : ℝ) * alphaStar = (z : ℝ) :=
  DecimalPeriodArithmetic.decimal_nonresonant
    AlphaRemarkTrial.LowerAssembly.alphaStar_gt_4323617
    NegSignProd.alphaStar_lt_upper_decimal hm hbound

end KsIndex.Staircase
