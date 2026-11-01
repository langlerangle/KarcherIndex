module

public import KsIndexLean.NegSignRationalTails
public import KsIndexLean.AlphaTrialTableData

@[expose] public section


/-! Bridge from verified table entries to rational tail-endpoint intervals:
given the three table-value facts at a covered frequency, the endpoint interval
holds with explicitly rational center and radius. -/

noncomputable section
namespace KsIndex.AlphaRemarkTrial
open PowerArc

theorem tailEndpoint_interval_table {N : ℕ} {tt : CoefficientTable}
    (hv : ValidCoefficientTable N tt)
    {r : Fin 25 → ℝ} {k : Fin 25 → ℤ} (hk : ∀ i, r i = ((k i : ℤ) : ℝ))
    (hk1 : ∀ i, 1 ≤ k i) (i : Fin 25)
    (hcov : (k i).natAbs / 2 ≤ N)
    {A Z E : ℤ}
    (hA : tableCellA tt i (k i) = A) (hZ : cellZ i (k i) = Z)
    (hE : tableCellE tt i (k i) = E)
    {cen rad : ℚ}
    (hcen : cen = (((k i : ℤ) : ℚ) + exponentQ i) * ((A : ℚ) * (Z : ℚ)) / 10 ^ 39)
    (hrad : rad = (((k i : ℤ) : ℚ) + exponentQ i) * (E : ℚ) / 10 ^ 39) :
    |tailEndpoint r i - ((cen : ℚ) : ℝ)| ≤ ((rad : ℚ) : ℝ) := by
  have hb := tailEndpoint_interval hk hk1 i
  have hcA : cellA i (k i) = A := by rw [← tableCellA_eq hv i (k i) hcov, hA]
  have hcE : cellE i (k i) = E := by rw [← tableCellE_eq hv i (k i) hcov, hE]
  have hcenter := integer_cell_center i (k i)
  have herror := integer_cell_error i (k i)
  rw [hcA, hZ] at hcenter
  rw [hcE] at herror
  rw [hcenter, herror] at hb
  have ecen : (((k i : ℤ) : ℝ) + exponent i) * (((A * Z : ℤ) : ℝ) / 10 ^ 39) =
      ((cen : ℚ) : ℝ) := by
    rw [hcen]
    push_cast [exponentQ_cast]
    ring
  have erad : (((k i : ℤ) : ℝ) + exponent i) * (((E : ℤ) : ℝ) / 10 ^ 39) =
      ((rad : ℚ) : ℝ) := by
    rw [hrad]
    push_cast [exponentQ_cast]
    ring
  rw [ecen, erad] at hb
  exact hb

end KsIndex.AlphaRemarkTrial
