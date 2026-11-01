module

public import KsIndexLean.SphericalEigenPotential
public import KsIndexLean.WeakRadialModeEquation

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

lemma radialJacobi_weak_mode_equation_normalized {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a b) (V : BoundedRealPotential) (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W)
    (hV : ∀ z ∈ (disk : Set ℂ), V.V z = W ‖z‖) (n : ℤ) (u : ComplexH1)
    (hu : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ →
      weakJacobi V u v = 0) :
    ((∫ r in Ioo a b, (r * deriv χ r : ℝ) • interiorDiskRadialMode a b u n r) +
      ∫ r in Ioo a b, ((n : ℝ)^2 * χ r / r) • interiorDiskMode hab u n r) -
      (∫ r in Ioo a b, (r * (χ r * W r)) • interiorDiskMode hab u n r) = 0 := by
  have h := weakJacobi_compactPolarTest_modes ha hab hb hχ hc hs n u V hW hV
  have hz := hu _ (compactPolarTestH1_zeroTrace ha hb hχ hs n Set.univ)
  rw [hz] at h
  have h := h.symm
  have hmid : (∫ r in Ioo a b, (χ r / r : ℝ) •
      (((2 * Real.pi : ℝ) : ℂ) * (n : ℂ)^2 *
        (starRingEnd ℂ) (interiorDiskMode hab u n r))) =
      ∫ r in Ioo a b, ((n : ℝ)^2 * χ r / r) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (interiorDiskMode hab u n r)) := by
    apply integral_congr_ae
    filter_upwards [] with r
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_intCast]
    ring
  rw [hmid, integral_real_weight_conj, integral_real_weight_conj, integral_real_weight_conj] at h
  have hC : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  have he : ((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ)
      (((∫ r in Ioo a b, (r * deriv χ r : ℝ) • interiorDiskRadialMode a b u n r) +
        ∫ r in Ioo a b, ((n : ℝ)^2 * χ r / r) • interiorDiskMode hab u n r) -
        (∫ r in Ioo a b, (r * (χ r * W r)) • interiorDiskMode hab u n r)) = 0 := by
    simpa only [map_sub, map_add, mul_sub, mul_add] using h
  have hz := (mul_eq_zero.mp he).resolve_left hC
  exact (starRingEnd ℂ).injective (hz.trans (map_zero (starRingEnd ℂ)).symm)

def sphericalEigenRadialCoefficient (k : ℕ) (lam : ℝ) (r : ℝ) : ℝ :=
  KsIndex.Radial.Vrad k r + lam * (4 / (1 + r ^ 2) ^ 2)

lemma sphericalEigenRadialCoefficient_smooth (k : ℕ) (lam : ℝ) :
    ContDiff ℝ ∞ (sphericalEigenRadialCoefficient k lam) := by
  apply (contDiff_Vrad k).add
  apply contDiff_const.mul
  exact ContDiff.div contDiff_const (by fun_prop) (fun r => by positivity)

lemma sphericalEigenPotential_radial (k : ℕ) (lam : ℝ) (z : ℂ) :
    (sphericalEigenPotential (surfacePotential k) lam).V z =
      sphericalEigenRadialCoefficient k lam ‖z‖ := by
  simp only [sphericalEigenPotential, surfacePotential, sphericalEigenRadialCoefficient,
    stereoAreaDensity_eq, KsIndex.Radial.potV_eq_Vrad]

/-- Every weak spherical eigenfunction satisfies its spectral-parameter radial
mode equation on every annulus, with no regularity assumption at the centre. -/
lemma sphericalEigen_weak_mode_equation {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a b) (k : ℕ) (lam : ℝ) (n : ℤ) (u : ComplexH1)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v)) :
    ((∫ r in Ioo a b, (r * deriv χ r : ℝ) • interiorDiskRadialMode a b u n r) +
      ∫ r in Ioo a b, ((n : ℝ)^2 * χ r / r) • interiorDiskMode hab u n r) -
      (∫ r in Ioo a b, (r * (χ r * sphericalEigenRadialCoefficient k lam r)) •
        interiorDiskMode hab u n r) = 0 := by
  apply radialJacobi_weak_mode_equation_normalized ha hab hb hχ hc hs
    (sphericalEigenPotential (surfacePotential k) lam) _
    (sphericalEigenRadialCoefficient_smooth k lam)
    (fun z _ => sphericalEigenPotential_radial k lam z) n u
  intro v hv
  exact (spherical_eigen_equation_iff _ lam u v).mp (hu v hv)

end KsIndex.Trace
