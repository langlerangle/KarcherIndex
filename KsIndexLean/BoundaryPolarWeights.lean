module

public import KsIndexLean.BoundaryPolarIntegration
public import KsIndexLean.CompactPolarWeights
public import KsIndexLean.CompactPolarWeakJet
public import Mathlib.Analysis.Calculus.Deriv.Support

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma integral_annulus_boundaryPolarTest_radial_deriv {a b c : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a c) (n : ℤ) (u : ComplexH1) :
    (∫ z in annulusSet a b, (starRingEnd ℂ) (radialField (Dxy (dxLp u) (dyLp u)) z) *
      (((deriv χ ‖z‖ : ℝ) : ℂ) * fourierAmbient n (nUnit z))) =
      ∫ r in Ioo a b, (r * deriv χ r : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (interiorDiskRadialMode a b u n r)) := by
  have h := integral_annulus_boundaryPolarTest_radial ha hab hb
    (contDiff_infty_iff_deriv.mp hχ).2 hc.deriv (tsupport_deriv_subset.trans hs) n u
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [compactPolarTest]
  ring

lemma integral_annulus_boundaryPolarTest_angular_weighted {a b c : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a c) (n : ℤ) (u : ComplexH1) :
    (∫ z in annulusSet a b, (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) *
      (starRingEnd ℂ) (angularField (Dxy (dxLp u) (dyLp u)) z) *
      ((n : ℂ) * Complex.I * compactPolarTest χ n z)) =
      ∫ r in Ioo a b, (χ r / r : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (n : ℂ)^2 *
          (starRingEnd ℂ) (interiorDiskMode hab u n r)) := by
  have hp := contDiff_radialProfile ha hχ hs
  have hps := tsupport_radialProfile_subset hs
  have h := integral_annulus_boundaryPolarTest_angular ha hab hb
    (contDiff_radialProfile ha hp hps)
    (hasCompactSupport_radialProfile (hasCompactSupport_radialProfile hc))
    (tsupport_radialProfile_subset hps) n u
  have hl : (∫ z in annulusSet a b, (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) *
      (starRingEnd ℂ) (angularField (Dxy (dxLp u) (dyLp u)) z) *
      ((n : ℂ) * Complex.I * compactPolarTest χ n z)) =
      ((n : ℂ) * Complex.I) * (∫ z in annulusSet a b, compactPolarTest (radialProfile (radialProfile χ)) n z *
        (starRingEnd ℂ) (angularField (Dxy (dxLp u) (dyLp u)) z)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [compactPolarTest_radialProfile_twice]
    ring
  rw [hl, h, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  have hr0 : r ≠ 0 := (ha.trans hr.1).ne'
  have hw : r * radialProfile (radialProfile χ) r = χ r / r := by
    dsimp only [radialProfile]
    field_simp
  rw [hw]
  simp only [Complex.real_smul, map_mul, map_intCast, Complex.conj_I]
  ring_nf
  simp [Complex.I_sq]


end KsIndex.Trace
