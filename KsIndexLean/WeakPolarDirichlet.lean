module

public import KsIndexLean.PolarJetInverse
public import KsIndexLean.InteriorDiskModes

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- The unnormalized radial/rotation frame has Gram matrix norm(z)^2 times
identity. This is polarized, with conjugation in the first slot. -/
lemma complex_frame_pairing (U V : ℂ →L[ℝ] ℂ) (z : ℂ) :
    (starRingEnd ℂ) (U z) * V z +
      (starRingEnd ℂ) (U (z * Complex.I)) * V (z * Complex.I) =
      (‖z‖ ^ 2 : ℂ) * ((starRingEnd ℂ) (U 1) * V 1 +
        (starRingEnd ℂ) (U Complex.I) * V Complex.I) := by
  have hn : (‖z‖ ^ 2 : ℂ) = (z.re : ℂ)^2 + (z.im : ℂ)^2 := by
    have hr : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    exact_mod_cast hr
  have hrot (L : ℂ →L[ℝ] ℂ) : L (z * Complex.I) =
      (-z.im) • L 1 + z.re • L Complex.I := by
    rw [complex_rotation_decomp, map_add, map_smul, map_smul]
  rw [hn, realLinear_coordinates U z, realLinear_coordinates V z, hrot U, hrot V]
  simp only [Complex.real_smul, map_add, map_mul, Complex.conj_ofReal]
  push_cast
  ring

lemma weakJet_polar_pairing (U V : ℂ → ℂ →L[ℝ] ℂ) {z : ℂ} (hz : z ≠ 0) :
    (starRingEnd ℂ) (U z 1) * V z 1 + (starRingEnd ℂ) (U z Complex.I) * V z Complex.I =
      (starRingEnd ℂ) (radialField U z) * radialField V z +
        ((‖z‖ ^ 2)⁻¹ : ℂ) * (starRingEnd ℂ) (angularField U z) * angularField V z := by
  have h := complex_frame_pairing (U z) (V z) z
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  rw [radialField_apply, radialField_apply, angularField_apply, angularField_apply]
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]
  push_cast
  field_simp
  linear_combination -h

/-- The actual weak disk Dirichlet form in polar components. The angular
component is differentiation along zI, hence the inverse-square radius. -/
lemma weakDirichlet_polar_integral (u v : ComplexH1) :
    dirichlet u v = ∫ z in (disk : Set ℂ),
      (starRingEnd ℂ) (radialField (Dxy (dxLp u) (dyLp u)) z) *
        radialField (Dxy (dxLp v) (dyLp v)) z +
      ((‖z‖ ^ 2)⁻¹ : ℂ) *
        (starRingEnd ℂ) (angularField (Dxy (dxLp u) (dyLp u)) z) *
        angularField (Dxy (dxLp v) (dyLp v)) z := by
  rw [dirichlet_integral]
  apply integral_congr_ae
  have hz : ∀ᵐ z : ℂ ∂volume.restrict (disk : Set ℂ), z ≠ 0 :=
    (show ∀ᵐ z : ℂ ∂volume, z ≠ 0 from ae_iff.mpr (by simp)).filter_mono
      (ae_mono Measure.restrict_le_self)
  filter_upwards [hz] with z hz
  have hx (w : ComplexH1) : dxCLM w = dxLp w := rfl
  have hy (w : ComplexH1) : dyCLM w = dyLp w := rfl
  rw [hx, hx, hy, hy]
  simpa only [Dxy_one, Dxy_I] using weakJet_polar_pairing
    (Dxy (dxLp u) (dyLp u)) (Dxy (dxLp v) (dyLp v)) hz

end KsIndex.Trace
