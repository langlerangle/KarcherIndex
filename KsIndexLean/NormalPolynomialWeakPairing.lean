module

public import KsIndexLean.FiniteNormalTestPairing
public import KsIndexLean.PolarFourierPairing

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

lemma circleFourierModeContinuous_toLp (n : ℤ) :
    ContinuousMap.toLp 2 circleMeasure ℂ (circleFourierModeContinuous n) = fourierTestLp n := by
  apply Lp.ext
  exact (ContinuousMap.coeFn_toLp circleMeasure (circleFourierModeContinuous n)).trans
    (fourierTestLp_coe n).symm

lemma inner_circleFourierPolynomial (f : Lp ℂ 2 circleMeasure)
    (s : Finset ℤ) (c : ℤ → ℂ) :
    inner ℂ f (ContinuousMap.toLp 2 circleMeasure ℂ (circleFourierPolynomial s c)) =
      ((2 * Real.pi : ℝ) : ℂ) * ∑ n ∈ s, (starRingEnd ℂ) (circleFourierCoeff f n) * c n := by
  simp only [circleFourierPolynomial, map_sum, map_smul, inner_sum, inner_smul_right,
    circleFourierModeContinuous_toLp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← inner_conj_symm, fourierTestLp_inner_unscaled, map_mul, Complex.conj_ofReal]
  ring

/-- Exact geometric L2 boundary pairing for finite-Fourier-trace weak tests. -/
lemma sphericalEigen_normal_pairing_finite_trace (k : ℕ) (lam : ℝ) (u : ComplexH1)
    (ht : u ∈ zeroTraceDomain Set.univ)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v))
    (s : Finset ℤ) (c : ℤ → ℂ) (v : ComplexH1)
    (hv : diskTraceCLM v = ContinuousMap.toLp 2 circleMeasure ℂ (circleFourierPolynomial s c)) :
    weakJacobi (sphericalEigenPotential (surfacePotential k) lam) u v =
      inner ℂ (ContinuousMap.toLp 2 circleMeasure ℂ (dirichletNormalPolynomial k lam u ht hu))
        (diskTraceCLM v) := by
  rw [sphericalEigen_finite_trace_pairing k lam u hu s c v hv, hv,
    inner_circleFourierPolynomial]
  simp only [← circleCoefficientCLM_apply, dirichletNormalPolynomial_coefficient]

/-- Tests with actual finite Fourier trace. They need not have finite angular
support in the disk. -/
def finiteFourierTraceTests : Set ComplexH1 :=
  {v | ∃ s : Finset ℤ, ∃ c : ℤ → ℂ,
    diskTraceCLM v = ContinuousMap.toLp 2 circleMeasure ℂ (circleFourierPolynomial s c)}

/-- Both sides are continuous in the full H1 test norm, so the identified
boundary pairing extends to the H1 closure of finite-trace tests. Density of
that test class is a separate obligation, not a hypothesis hidden here. -/
theorem sphericalEigen_normal_pairing_closure (k : ℕ) (lam : ℝ) (u : ComplexH1)
    (ht : u ∈ zeroTraceDomain Set.univ)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v))
    (v : ComplexH1) (hv : v ∈ closure finiteFourierTraceTests) :
    weakJacobi (sphericalEigenPotential (surfacePotential k) lam) u v =
      inner ℂ (ContinuousMap.toLp 2 circleMeasure ℂ (dirichletNormalPolynomial k lam u ht hu))
        (diskTraceCLM v) := by
  have hc : IsClosed {v : ComplexH1 |
      weakJacobi (sphericalEigenPotential (surfacePotential k) lam) u v =
        inner ℂ (ContinuousMap.toLp 2 circleMeasure ℂ (dirichletNormalPolynomial k lam u ht hu))
          (diskTraceCLM v)} :=
    isClosed_eq (continuous_weakJacobi_fixed_left _ u)
      (continuous_const.inner diskTraceCLM.continuous)
  apply closure_minimal (t := {v : ComplexH1 | _}) ?_ hc hv
  rintro w ⟨s, c, hw⟩
  exact sphericalEigen_normal_pairing_finite_trace k lam u ht hu s c w hw

end KsIndex.Trace
