module

public import KsIndexLean.CompactPolarIntegration
public import KsIndexLean.CompactPolarWeakJet
public import Mathlib.Analysis.Calculus.Deriv.Support

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma integral_compactPolarTest_radial_deriv {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a b) (n : ℤ) (u : ComplexH1) :
    (∫ z, (starRingEnd ℂ) (radialField (Dxy (dxLp u) (dyLp u)) z) *
      (((deriv χ ‖z‖ : ℝ) : ℂ) * fourierAmbient n (nUnit z))) =
      ∫ r in Ioo a b, (r * deriv χ r : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (interiorDiskRadialMode a b u n r)) := by
  have h := integral_compactPolarTest_radial ha hab hb
    (contDiff_infty_iff_deriv.mp hχ).2 hc.deriv (tsupport_deriv_subset.trans hs) n u
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [compactPolarTest]
  ring

/-- Applying `radialProfile` twice multiplies the test by the inverse squared radius.
This is an algebraic identity with total division; smoothness is used separately below
for profiles supported away from zero. -/
lemma compactPolarTest_radialProfile_twice (χ : ℝ → ℝ) (n : ℤ) (z : ℂ) :
    compactPolarTest (radialProfile (radialProfile χ)) n z =
      (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) * compactPolarTest χ n z := by
  simp only [compactPolarTest, radialProfile, div_eq_mul_inv, Complex.ofReal_mul,
    Complex.ofReal_inv, Complex.ofReal_pow]
  ring

lemma integral_compactPolarTest_angular_weighted {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a b) (n : ℤ) (u : ComplexH1) :
    (∫ z, (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) *
      (starRingEnd ℂ) (angularField (Dxy (dxLp u) (dyLp u)) z) *
      ((n : ℂ) * Complex.I * compactPolarTest χ n z)) =
      ∫ r in Ioo a b, (χ r / r : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (n : ℂ)^2 *
          (starRingEnd ℂ) (interiorDiskMode hab u n r)) := by
  have hp := contDiff_radialProfile ha hχ hs
  have hps := tsupport_radialProfile_subset hs
  have h := integral_compactPolarTest_angular ha hab hb
    (contDiff_radialProfile ha hp hps)
    (hasCompactSupport_radialProfile (hasCompactSupport_radialProfile hc))
    (tsupport_radialProfile_subset hps) n u
  have hl : (∫ z, (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) *
      (starRingEnd ℂ) (angularField (Dxy (dxLp u) (dyLp u)) z) *
      ((n : ℂ) * Complex.I * compactPolarTest χ n z)) =
      ((n : ℂ) * Complex.I) * (∫ z, compactPolarTest (radialProfile (radialProfile χ)) n z *
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

lemma integrable_compactPolarTest_mul {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a b) (n : ℤ) {f : ℂ → ℂ}
    (hf : MemLp f 2 (volume.restrict (annulusSet a b))) :
    Integrable (fun z => compactPolarTest χ n z * f z) volume := by
  apply (integrableOn_compactPolarTest_mul ha hab hχ hc hs n hf).integrable_of_forall_notMem_eq_zero
  intro z hz
  rw [image_eq_zero_of_notMem_tsupport (fun hm => hz (compactPolarTest_annular_support hs n hm)),
    zero_mul]

/-- The full weak disk Dirichlet pairing reduces to the radial and angular mode terms. -/
lemma weakDirichlet_compactPolarTest_modes {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a b) (n : ℤ) (u : ComplexH1) :
    dirichlet u (compactPolarTestH1 ha hχ hs n) =
      (∫ r in Ioo a b, (r * deriv χ r : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (interiorDiskRadialMode a b u n r))) +
      ∫ r in Ioo a b, (χ r / r : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (n : ℂ)^2 *
          (starRingEnd ℂ) (interiorDiskMode hab u n r)) := by
  let R := fun z : ℂ => (starRingEnd ℂ) (radialField (Dxy (dxLp u) (dyLp u)) z) *
    (((deriv χ ‖z‖ : ℝ) : ℂ) * fourierAmbient n (nUnit z))
  let T := fun z : ℂ => (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) *
    (starRingEnd ℂ) (angularField (Dxy (dxLp u) (dyLp u)) z) *
    ((n : ℂ) * Complex.I * compactPolarTest χ n z)
  have hm : MemLp (radialField (Dxy (dxLp u) (dyLp u))) 2
      (volume.restrict (annulusSet a b)) := by
    apply memLp_radialField ha
    · simpa using interiorAnnulus_memLp hb (dxLp u)
    · simpa using interiorAnnulus_memLp hb (dyLp u)
  have hR : Integrable R volume := by
    have h := integrable_compactPolarTest_mul ha hab
      (contDiff_infty_iff_deriv.mp hχ).2 hc.deriv (tsupport_deriv_subset.trans hs) n hm.star
    apply h.congr
    filter_upwards [] with z
    dsimp only [R, compactPolarTest]
    change ((deriv χ ‖z‖ : ℝ) : ℂ) * fourierAmbient n (nUnit z) *
      (starRingEnd ℂ) (radialField (Dxy (dxLp u) (dyLp u)) z) = _
    ring
  have hT : Integrable T volume := by
    have hp := contDiff_radialProfile ha hχ hs
    have hps := tsupport_radialProfile_subset hs
    have h := (integrable_compactPolarTest_mul ha hab
      (contDiff_radialProfile ha hp hps)
      (hasCompactSupport_radialProfile (hasCompactSupport_radialProfile hc))
      (tsupport_radialProfile_subset hps) n (interiorDiskAngularField_memLp hb u).star).const_mul
        ((n : ℂ) * Complex.I)
    apply h.congr
    filter_upwards [] with z
    dsimp only [T]
    change ((n : ℂ) * Complex.I) *
      (compactPolarTest (radialProfile (radialProfile χ)) n z *
        (starRingEnd ℂ) (angularField (Dxy (dxLp u) (dyLp u)) z)) = _
    rw [compactPolarTest_radialProfile_twice]
    ring
  have hzero : ∀ z : ℂ, z ∉ (disk : Set ℂ) → R z + T z = 0 := by
    intro z hz
    have hn : ‖z‖ ∉ tsupport χ := fun h => hz (interiorAnnulus_subset_disk hb (hs h))
    dsimp only [R, T, compactPolarTest]
    rw [deriv_eq_zero_of_notMem_tsupport hn, image_eq_zero_of_notMem_tsupport hn]
    simp
  rw [weakDirichlet_compactPolarTest ha hχ hs n u]
  have he : (∫ z in (disk : Set ℂ), R z + T z) = ∫ z, R z + T z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_inv]
  change (∫ z in (disk : Set ℂ), R z + T z) = _
  rw [he, integral_add hR hT]
  exact congrArg₂ (· + ·) (integral_compactPolarTest_radial_deriv ha hab hb hχ hc hs n u)
    (integral_compactPolarTest_angular_weighted ha hab hb hχ hc hs n u)

end KsIndex.Trace
