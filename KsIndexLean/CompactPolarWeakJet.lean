module

public import KsIndexLean.CompactPolarTestDerivatives
public import KsIndexLean.WeakPolarDirichlet

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma globalSmoothH1_jet (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) :
    (fun z => Dxy (dxLp (globalSmoothH1 f hf)) (dyLp (globalSmoothH1 f hf)) z) =ᵐ[
      volume.restrict (disk : Set ℂ)] fderiv ℝ f := by
  have hx := globalSmoothH1_dx f hf
  have hy := globalSmoothH1_dy f hf
  change (dxLp (globalSmoothH1 f hf) : ℂ → ℂ) =ᵐ[_] _ at hx
  change (dyLp (globalSmoothH1 f hf) : ℂ → ℂ) =ᵐ[_] _ at hy
  filter_upwards [hx, hy] with z hz1 hzI
  ext w
  rw [Dxy_apply, hz1, hzI, realLinear_coordinates (fderiv ℝ f z) w]

lemma compactPolarTest_unit_radial {a b : ℝ} (ha : 0 < a) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ Ioo a b) (n : ℤ) {z : ℂ} (hz : z ≠ 0) :
    fderiv ℝ (compactPolarTest χ n) z (nUnit z) =
      ((deriv χ ‖z‖ : ℝ) : ℂ) * fourierAmbient n (nUnit z) := by
  let w : Circle₁ := ⟨nUnit z, mem_sphere_zero_iff_norm.mpr (norm_nUnit hz)⟩
  have he : ‖z‖ • (w : ℂ) = z := by
    change ‖z‖ • (‖z‖⁻¹ • z) = z
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
  have h := compactPolarTest_fderiv_radial ha hχ hχs n (norm_pos_iff.mpr hz) w
  rw [he] at h
  exact h

lemma compactPolarTestH1_radial_ae {a b : ℝ} (ha : 0 < a) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ Ioo a b) (n : ℤ) :
    radialField (Dxy (dxLp (compactPolarTestH1 ha hχ hχs n))
      (dyLp (compactPolarTestH1 ha hχ hχs n))) =ᵐ[volume.restrict (disk : Set ℂ)]
      (fun z => ((deriv χ ‖z‖ : ℝ) : ℂ) * fourierAmbient n (nUnit z)) := by
  have hz : ∀ᵐ z : ℂ ∂volume.restrict (disk : Set ℂ), z ≠ 0 :=
    (show ∀ᵐ z : ℂ ∂volume, z ≠ 0 from ae_iff.mpr (by simp)).filter_mono
      (ae_mono Measure.restrict_le_self)
  filter_upwards [globalSmoothH1_jet (compactPolarTest χ n)
    (compactPolarTest_smooth ha hχ hχs n), hz] with z hj hz
  dsimp only [compactPolarTestH1]
  rw [radialField_apply, hj, ← map_smul]
  exact compactPolarTest_unit_radial ha hχ hχs n hz

lemma compactPolarTestH1_angular_ae {a b : ℝ} (ha : 0 < a) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ Ioo a b) (n : ℤ) :
    angularField (Dxy (dxLp (compactPolarTestH1 ha hχ hχs n))
      (dyLp (compactPolarTestH1 ha hχ hχs n))) =ᵐ[volume.restrict (disk : Set ℂ)]
      (fun z => (n : ℂ) * Complex.I * compactPolarTest χ n z) := by
  filter_upwards [globalSmoothH1_jet (compactPolarTest χ n)
    (compactPolarTest_smooth ha hχ hχs n)] with z hj
  dsimp only [compactPolarTestH1]
  rw [angularField_apply, hj]
  exact compactPolarTest_fderiv_angular ha hχ hχs n z

lemma weakDirichlet_compactPolarTest {a b : ℝ} (ha : 0 < a) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ Ioo a b) (n : ℤ) (u : ComplexH1) :
    dirichlet u (compactPolarTestH1 ha hχ hχs n) = ∫ z in (disk : Set ℂ),
      (starRingEnd ℂ) (radialField (Dxy (dxLp u) (dyLp u)) z) *
        (((deriv χ ‖z‖ : ℝ) : ℂ) * fourierAmbient n (nUnit z)) +
      ((‖z‖ ^ 2)⁻¹ : ℂ) * (starRingEnd ℂ) (angularField (Dxy (dxLp u) (dyLp u)) z) *
        ((n : ℂ) * Complex.I * compactPolarTest χ n z) := by
  rw [weakDirichlet_polar_integral]
  apply integral_congr_ae
  filter_upwards [compactPolarTestH1_radial_ae ha hχ hχs n,
    compactPolarTestH1_angular_ae ha hχ hχs n] with z hr ht
  rw [hr, ht]

lemma weakJacobi_compactPolarTest {a b : ℝ} (ha : 0 < a) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ Ioo a b)
    (n : ℤ) (V : BoundedRealPotential) (u : ComplexH1) :
    weakJacobi V u (compactPolarTestH1 ha hχ hχs n) =
      (∫ z in (disk : Set ℂ),
        (starRingEnd ℂ) (radialField (Dxy (dxLp u) (dyLp u)) z) *
          (((deriv χ ‖z‖ : ℝ) : ℂ) * fourierAmbient n (nUnit z)) +
        ((‖z‖ ^ 2)⁻¹ : ℂ) * (starRingEnd ℂ) (angularField (Dxy (dxLp u) (dyLp u)) z) *
          ((n : ℂ) * Complex.I * compactPolarTest χ n z)) -
      ∫ z in (disk : Set ℂ), (V.V z : ℂ) * (starRingEnd ℂ) (valueCLM u z) *
        compactPolarTest χ n z := by
  rw [weakJacobi, weakDirichlet_compactPolarTest ha hχ hχs n u, potential_integral]
  congr 1
  apply integral_congr_ae
  filter_upwards [globalSmoothH1_value (compactPolarTest χ n)
    (compactPolarTest_smooth ha hχ hχs n)] with z hz
  change (V.V z : ℂ) * (starRingEnd ℂ) (valueCLM u z) *
    valueCLM (globalSmoothH1 (compactPolarTest χ n) (compactPolarTest_smooth ha hχ hχs n)) z = _
  rw [hz]

end KsIndex.Trace
