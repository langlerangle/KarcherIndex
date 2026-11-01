module

public import KsIndexLean.SphericalEigenNeumannFlux

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

/-- The exact weak boundary pairing extracts the normal Fourier coefficient.
The factor 2π and complex conjugation follow the project's form convention. -/
lemma sphericalEigen_boundary_fourier_flux_pairing {a c : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (k : ℕ) (lam : ℝ) (u : ComplexH1) (n : ℤ)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a c) (hχ1 : χ 1 = 1) :
    weakJacobi (sphericalEigenPotential (surfacePotential k) lam) u (compactPolarTestH1 ha hχ hs n) =
      ((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (eigenDiskNormalMode k lam u n) := by
  have hp := weakJacobi_boundaryPolarTest_modes ha ha1 hχ hc hs n u
    (sphericalEigenPotential (surfacePotential k) lam)
    (sphericalEigenRadialCoefficient_smooth k lam)
    (fun z _ => sphericalEigenPotential_radial k lam z)
  have hmid : (∫ r in Ioo a 1, (χ r / r : ℝ) •
      (((2 * Real.pi : ℝ) : ℂ) * (n : ℂ)^2 *
        (starRingEnd ℂ) (interiorDiskMode ha1 u n r))) =
      ∫ r in Ioo a 1, ((n : ℝ)^2 * χ r / r) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (interiorDiskMode ha1 u n r)) := by
    apply integral_congr_ae
    filter_upwards [] with r
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_intCast]
    ring
  rw [hmid, integral_real_weight_conj, integral_real_weight_conj, integral_real_weight_conj] at hp
  have hχa : χ a = 0 := image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl a) (hs h).1)
  rw [sphericalEigen_normalMode_eq_green ha ha1 k lam u n hu hχ hχa hχ1,
    sphericalEigen_green_eq_mode_integrals ha ha1 k lam u n hu hχ]
  simpa only [map_sub, map_add, mul_sub, mul_add] using hp

/-- The same formula states the unshifted eigenvalue residual explicitly. -/
lemma sphericalEigen_boundary_residual_flux_pairing {a c : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (k : ℕ) (lam : ℝ) (u : ComplexH1) (n : ℤ)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a c) (hχ1 : χ 1 = 1) :
    weakJacobi (surfacePotential k) u (compactPolarTestH1 ha hχ hs n) -
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u)
        (weightedDiskValueCLM (compactPolarTestH1 ha hχ hs n)) =
      ((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (eigenDiskNormalMode k lam u n) := by
  rw [← weakJacobi_sphericalEigenPotential]
  exact sphericalEigen_boundary_fourier_flux_pairing ha ha1 k lam u n hu hχ hc hs hχ1

end KsIndex.Trace
