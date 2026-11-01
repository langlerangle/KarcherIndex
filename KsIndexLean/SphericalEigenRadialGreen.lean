module

public import KsIndexLean.SphericalEigenModeCompatibility

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

/-- Radial integration by parts retains both endpoint flux terms. No support
condition on the test function at the outer boundary is imposed. -/
lemma sphericalEigen_radial_green {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (k : ℕ) (lam : ℝ) (u : ComplexH1) (n : ℤ)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    (∫ r in a..b, (deriv χ r) • eigenDiskFluxRepresentative hab k lam u n r +
      χ r • eigenDiskModeRHS hab k lam u n r) =
      χ b • eigenDiskFluxRepresentative hab k lam u n b -
      χ a • eigenDiskFluxRepresentative hab k lam u n a := by
  have hf := eigenDiskFluxRepresentative_continuousOn ha hab hb k lam u n
  have hg := eigenDiskModeRHS_continuousOn ha hab hb k lam u n
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le
    (hχ.continuous.continuousOn.smul hf)
  · intro r hr
    simpa only [add_comm] using (hχ.differentiable (by simp) r).hasDerivAt.smul
      (eigenDiskFluxRepresentative_hasDerivAt ha hab hb k lam u n hr)
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab.le]
    have hd : ContinuousOn (deriv χ) (Icc a b) :=
      (hχ.continuous_deriv (by simp)).continuousOn
    exact hd.smul hf |>.add (hχ.continuous.continuousOn.smul hg)

/-- With a test equal to zero at the inner endpoint and one at the outer
boundary, the radial Green integral is the canonical normal coefficient. -/
lemma sphericalEigen_normalMode_eq_green {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (k : ℕ) (lam : ℝ) (u : ComplexH1) (n : ℤ)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχa : χ a = 0) (hχ1 : χ 1 = 1) :
    eigenDiskNormalMode k lam u n =
      ∫ r in a..1, (deriv χ r) • eigenDiskFluxRepresentative ha1 k lam u n r +
        χ r • eigenDiskModeRHS ha1 k lam u n r := by
  have h := sphericalEigen_radial_green ha ha1 le_rfl k lam u n hχ
  rw [hχa, hχ1, zero_smul, one_smul, sub_zero,
    eigenDiskFluxRepresentative_one ha ha1 k lam u n hu] at h
  exact h.symm

end KsIndex.Trace
