module

public import KsIndexLean.FiniteFourierReconstruction
public import KsIndexLean.WeakEigenTraceFourierSupport
public import KsIndexLean.SphericalEigenNeumannFlux

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

/-- A full Neumann weak spherical eigenfunction whose actual trace vanishes
on a nonempty open arc must vanish identically. No smoothness or finite-mode
hypothesis is imposed on the eigenfunction. -/
theorem sphericalEigen_neumann_openArc_eq_zero (k : ℕ) (lam : ℝ) (u : ComplexH1)
    (hu : ∀ v : ComplexH1, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v))
    (A : Set Circle₁) (hA : IsOpen A) (hne : A.Nonempty)
    (hz : (diskTraceCLM u : Circle₁ → ℂ) =ᵐ[circleMeasure.restrict A] 0) : u = 0 := by
  apply sphericalEigen_neumann_zeroTrace_eq_zero k lam u hu
  exact circleL2_eq_zero_of_finite_support_open_ae (diskTraceCLM u)
    (sphericalEigen_neumann_trace_finite_support k lam u hu) A hA hne hz

/-- The same uniqueness result in the project's actual zero-trace domain API. -/
theorem sphericalEigen_neumann_mem_zeroTrace_eq_zero (k : ℕ) (lam : ℝ) (u : ComplexH1)
    (hu : ∀ v : ComplexH1, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v))
    (A : Set Circle₁) (hA : IsOpen A) (hne : A.Nonempty)
    (hz : u ∈ zeroTraceDomain A) : u = 0 :=
  sphericalEigen_neumann_openArc_eq_zero k lam u hu A hA hne ((mem_zeroTraceDomain A u).mp hz)

end KsIndex.Trace
