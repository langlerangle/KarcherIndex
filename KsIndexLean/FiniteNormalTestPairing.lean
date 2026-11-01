module

public import KsIndexLean.DirichletNormalPolynomial

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

/-- Exact residual pairing for any weak test whose actual trace is a finite
Fourier polynomial. The bulk test need not be the canonical extension. -/
lemma sphericalEigen_finite_trace_pairing (k : ℕ) (lam : ℝ) (u : ComplexH1)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v))
    (s : Finset ℤ) (c : ℤ → ℂ) (v : ComplexH1)
    (hv : diskTraceCLM v = ContinuousMap.toLp 2 circleMeasure ℂ (circleFourierPolynomial s c)) :
    weakJacobi (sphericalEigenPotential (surfacePotential k) lam) u v =
      ((2 * Real.pi : ℝ) : ℂ) * ∑ n ∈ s, (starRingEnd ℂ) (eigenDiskNormalMode k lam u n) * c n := by
  let V := sphericalEigenPotential (surfacePotential k) lam
  let L : ComplexH1 →ₗ[ℂ] ℂ :=
    { toFun := weakJacobi V u
      map_add' := weakJacobi_add_right V u
      map_smul' := fun a v => weakJacobi_smul_right V a u v }
  let w : ComplexH1 := ∑ n ∈ s, c n • globalSmoothH1 (fourierAmbient n) (contDiff_fourierAmbient n)
  have hw : diskTraceCLM w = diskTraceCLM v := by
    rw [hv]
    simp only [w, circleFourierPolynomial, map_sum, map_smul, smoothFourier_trace_eq]
  rw [← weakJacobi_eq_of_trace_eq V u
    (fun v hv => (spherical_eigen_equation_iff _ lam u v).mp (hu v hv)) w v hw]
  change L w = _
  simp only [w, map_sum, map_smul, smul_eq_mul]
  change (∑ n ∈ s, c n * weakJacobi V u
    (globalSmoothH1 (fourierAmbient n) (contDiff_fourierAmbient n))) = _
  dsimp only [V]
  simp_rw [sphericalEigen_fourier_extension_flux_pairing k lam u _ hu]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

end KsIndex.Trace
