module

public import KsIndexLean.AlphaLowModeTable

@[expose] public section


/-! Reuse checked sample pairs across the four direct residual accumulations. -/
namespace KsIndex.AlphaRemarkTrial

def cachedLowLinearNumerator (a : ℤ → ℤ) (p : Finset ℤ) (n : ℤ) : ℤ :=
  ∑ m ∈ p, (rationalKernelWeight n m).num * a m /
    ((rationalKernelWeight n m).den : ℤ)

def cachedLowLinearRadius (e : ℤ → ℤ) (p : Finset ℤ) (n : ℤ) : ℤ :=
  ∑ m ∈ p, (|(rationalKernelWeight n m).num| * e m /
    ((rationalKernelWeight n m).den : ℤ) + 2)

theorem cachedLowLinearNumerator_eq (t : CoefficientTable) (p : Finset ℤ) (n : ℤ)
    (a : ℤ → ℤ) (ha : ∀ m ∈ p, a m = tableSampleNumerator t (2*m+1)) :
    cachedLowLinearNumerator a p n = tableLowLinearNumerator t p n := by
  apply Finset.sum_congr rfl
  intro m hm
  rw [ha m hm]

theorem cachedLowLinearRadius_eq (t : CoefficientTable) (p : Finset ℤ) (n : ℤ)
    (e : ℤ → ℤ) (he : ∀ m ∈ p, e m = tableSampleRadius t (2*m+1)) :
    cachedLowLinearRadius e p n = tableLowLinearRadius t p n := by
  apply Finset.sum_congr rfl
  intro m hm
  rw [he m hm]

/-- A checked sample cache retains the actual convolution error certificate. -/
theorem transpose_finite_cache_bound {N : ℕ} {t : CoefficientTable}
    (ht : ValidCoefficientTable N t) (p : Finset ℤ) (n : ℤ)
    (hc : ∀ m ∈ p, SampleCovered N (2*m+1)) (a e : ℤ → ℤ)
    (ha : ∀ m ∈ p, a m = tableSampleNumerator t (2*m+1))
    (he : ∀ m ∈ p, e m = tableSampleRadius t (2*m+1)) :
    |(∑ m ∈ p, transposeTerm n m) -
      (2/Real.pi)*((cachedLowLinearNumerator a p n : ℝ)/10^51)| ≤
      (2/Real.pi)*((cachedLowLinearRadius e p n : ℝ)/10^51) := by
  rw [cachedLowLinearNumerator_eq t p n a ha, cachedLowLinearRadius_eq t p n e he]
  exact transpose_finite_table_bound ht p n hc

end KsIndex.AlphaRemarkTrial
