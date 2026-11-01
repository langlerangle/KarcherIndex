module

public import KsIndexLean.NormalizedJacobiModes

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.DtNCircle

private lemma weakJacobi_zero_left (V : BoundedRealPotential) (v : ComplexH1) :
    weakJacobi V 0 v = 0 := by
  simpa only [zero_smul, map_zero, zero_mul] using weakJacobi_smul_left V (0 : ℂ) 0 v

/-- Finite physical-coefficient partial sums for the mean-zero Jacobi extension. -/
def finiteJacobiExtension {k : ℕ} (hk : 2 ≤ k) (s : Finset NZ) (a : NZ → ℂ) : ComplexH1 :=
  ∑ n ∈ s, a n • normalizedJacobiMode hk n

lemma finiteJacobiExtension_trace {k : ℕ} (hk : 2 ≤ k) (s : Finset NZ) (a : NZ → ℂ) :
    diskTraceCLM (finiteJacobiExtension hk s a) = ∑ n ∈ s, a n • fourierTestLp n := by
  simp only [finiteJacobiExtension, map_sum, map_smul, normalizedJacobiMode_trace]

/-- The finite extension retains the exact normal flux against arbitrary H1 tests. -/
lemma finiteJacobiExtension_weak_green {k : ℕ} (hk : 2 ≤ k) (s : Finset NZ)
    (a : NZ → ℂ) (v : ComplexH1) :
    weakJacobi (surfacePotential k) (finiteJacobiExtension hk s a) v =
      inner ℂ (∑ n ∈ s, (a n * (dtnSymbol k n : ℂ)) • fourierTestLp n) (diskTraceCLM v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [finiteJacobiExtension, weakJacobi_zero_left]
  | @insert n s hn ih =>
    simp only [finiteJacobiExtension, Finset.sum_insert hn] at ih ⊢
    rw [weakJacobi_add_left, weakJacobi_smul_left, normalizedJacobiMode_weak_green,
      ih, inner_add_left, ← inner_smul_left, smul_smul]

lemma finiteJacobiExtension_weak_zeroTrace {k : ℕ} (hk : 2 ≤ k) (s : Finset NZ)
    (a : NZ → ℂ) (v : ComplexH1) (hv : v ∈ zeroTraceDomain Set.univ) :
    weakJacobi (surfacePotential k) (finiteJacobiExtension hk s a) v = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [finiteJacobiExtension, weakJacobi_zero_left]
  | @insert n s hn ih =>
    simp only [finiteJacobiExtension, Finset.sum_insert hn] at ih ⊢
    rw [weakJacobi_add_left, weakJacobi_smul_left, normalizedJacobiMode_weak_zeroTrace hk n v hv,
      ih, mul_zero, add_zero]

end KsIndex.Trace
