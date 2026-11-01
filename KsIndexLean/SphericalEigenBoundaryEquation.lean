module

public import KsIndexLean.BoundaryPolarJacobi
public import KsIndexLean.SphericalEigenRadial

@[expose] public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

lemma radialJacobi_boundary_mode_equation_normalized {a c : ℝ}
    (ha : 0 < a) (hab : a < 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a c) (V : BoundedRealPotential) (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W)
    (hV : ∀ z ∈ (disk : Set ℂ), V.V z = W ‖z‖) (n : ℤ) (u : ComplexH1)
    (hu : ∀ v : ComplexH1,
      weakJacobi V u v = 0) :
    ((∫ r in Ioo a 1, (r * deriv χ r : ℝ) • interiorDiskRadialMode a 1 u n r) +
      ∫ r in Ioo a 1, ((n : ℝ)^2 * χ r / r) • interiorDiskMode hab u n r) -
      (∫ r in Ioo a 1, (r * (χ r * W r)) • interiorDiskMode hab u n r) = 0 := by
  have h := weakJacobi_boundaryPolarTest_modes ha hab hχ hc hs n u V hW hV
  have hz := hu (compactPolarTestH1 ha hχ hs n)
  rw [hz] at h
  have h := h.symm
  have hmid : (∫ r in Ioo a 1, (χ r / r : ℝ) •
      (((2 * Real.pi : ℝ) : ℂ) * (n : ℂ)^2 *
        (starRingEnd ℂ) (interiorDiskMode hab u n r))) =
      ∫ r in Ioo a 1, ((n : ℝ)^2 * χ r / r) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (interiorDiskMode hab u n r)) := by
    apply integral_congr_ae
    filter_upwards [] with r
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_intCast]
    ring
  rw [hmid, integral_real_weight_conj, integral_real_weight_conj, integral_real_weight_conj] at h
  have hC : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  have he : ((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ)
      (((∫ r in Ioo a 1, (r * deriv χ r : ℝ) • interiorDiskRadialMode a 1 u n r) +
        ∫ r in Ioo a 1, ((n : ℝ)^2 * χ r / r) • interiorDiskMode hab u n r) -
        (∫ r in Ioo a 1, (r * (χ r * W r)) • interiorDiskMode hab u n r)) = 0 := by
    simpa only [map_sub, map_add, mul_sub, mul_add] using h
  have hz := (mul_eq_zero.mp he).resolve_left hC
  exact (starRingEnd ℂ).injective (hz.trans (map_zero (starRingEnd ℂ)).symm)


/-- A full Neumann weak eigenfunction satisfies the radial test equation
for cutoffs that may reach the outer boundary. -/
lemma sphericalEigen_boundary_mode_equation {a c : ℝ}
    (ha : 0 < a) (hab : a < 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a c) (k : ℕ) (lam : ℝ) (n : ℤ) (u : ComplexH1)
    (hu : ∀ v : ComplexH1, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v)) :
    ((∫ r in Ioo a 1, (r * deriv χ r : ℝ) • interiorDiskRadialMode a 1 u n r) +
      ∫ r in Ioo a 1, ((n : ℝ)^2 * χ r / r) • interiorDiskMode hab u n r) -
      (∫ r in Ioo a 1, (r * (χ r * sphericalEigenRadialCoefficient k lam r)) •
        interiorDiskMode hab u n r) = 0 := by
  apply radialJacobi_boundary_mode_equation_normalized ha hab hχ hc hs
    (sphericalEigenPotential (surfacePotential k) lam) _
    (sphericalEigenRadialCoefficient_smooth k lam)
    (fun z _ => sphericalEigenPotential_radial k lam z) n u
  intro v
  exact (spherical_eigen_equation_iff _ lam u v).mp (hu v)

end KsIndex.Trace
