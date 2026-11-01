module

public import KsIndexLean.AlphaLowModeLinear
public import KsIndexLean.AlphaTrialTableData

@[expose] public section


/-! Shared coefficient tables for direct residual linear accumulations. -/
namespace KsIndex.AlphaRemarkTrial

def tableLowLinearNumerator (t : CoefficientTable) (p : Finset ℤ) (n : ℤ) : ℤ :=
  ∑ m ∈ p, (rationalKernelWeight n m).num * tableSampleNumerator t (2*m+1) /
    ((rationalKernelWeight n m).den : ℤ)

def tableLowLinearRadius (t : CoefficientTable) (p : Finset ℤ) (n : ℤ) : ℤ :=
  ∑ m ∈ p, (|(rationalKernelWeight n m).num| * tableSampleRadius t (2*m+1) /
    ((rationalKernelWeight n m).den : ℤ) + 2)

theorem tableLowLinearNumerator_eq {N : ℕ} {t : CoefficientTable}
    (ht : ValidCoefficientTable N t) (p : Finset ℤ) (n : ℤ)
    (hc : ∀ m ∈ p, SampleCovered N (2*m+1)) :
    tableLowLinearNumerator t p n = lowLinearNumerator p n := by
  apply Finset.sum_congr rfl
  intro m hm
  rw [tableSampleNumerator_eq ht (hc m hm)]

theorem tableLowLinearRadius_eq {N : ℕ} {t : CoefficientTable}
    (ht : ValidCoefficientTable N t) (p : Finset ℤ) (n : ℤ)
    (hc : ∀ m ∈ p, SampleCovered N (2*m+1)) :
    tableLowLinearRadius t p n = lowLinearRadius p n := by
  apply Finset.sum_congr rfl
  intro m hm
  rw [tableSampleRadius_eq ht (hc m hm)]

/-- Table acceleration preserves the actual analytic convolution certificate. -/
theorem transpose_finite_table_bound {N : ℕ} {t : CoefficientTable}
    (ht : ValidCoefficientTable N t) (p : Finset ℤ) (n : ℤ)
    (hc : ∀ m ∈ p, SampleCovered N (2*m+1)) :
    |(∑ m ∈ p, transposeTerm n m) -
      (2/Real.pi)*((tableLowLinearNumerator t p n : ℝ)/10^51)| ≤
      (2/Real.pi)*((tableLowLinearRadius t p n : ℝ)/10^51) := by
  rw [tableLowLinearNumerator_eq ht p n hc, tableLowLinearRadius_eq ht p n hc]
  exact transpose_finite_integer_bound p n

/-- Coverage for all odd frequencies in the paired convolution window. -/
theorem low_window_covered (T N : ℕ) (hN : T+3 ≤ N) :
    ∀ m ∈ Finset.Ico (-(T : ℤ)) T, SampleCovered N (2*m+1) := by
  intro m hm
  have hm' := Finset.mem_Ico.mp hm
  apply sampleCovered_of_bound
  have h : (2*m+1).natAbs ≤ 2*T-1 := by omega
  omega

end KsIndex.AlphaRemarkTrial
