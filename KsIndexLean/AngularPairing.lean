module

public import KsIndexLean.AngularPolarTest
public import KsIndexLean.PolarPairingIdentity

@[expose] public section


open Set MeasureTheory
open scoped Distributions ContDiff

noncomputable section
namespace KsIndex.Trace

lemma integrableOn_polarTest_smul {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a b) {H : ℂ → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    {u : ℂ → ℂ} (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    IntegrableOn (fun z => polarTest χ H z • u z) (annulusSet a b) volume := by
  have hp := (contDiff_polarTest ha hχ hs hH).continuous
  obtain ⟨C, hC⟩ := (hasCompactSupport_polarTest hc H).exists_bound_of_continuous hp
  exact integrableOn_bdd_smul ha hab hp.aestronglyMeasurable.restrict
    (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hC z)) hu

/-- Compact polar tests have a genuine Fubini factorization with the radius Jacobian. -/
lemma integral_polarTest_smul {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a b) {H : ℂ → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    {u : ℂ → ℂ} (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    (∫ z, polarTest χ H z • u z) =
      ∫ t in Ioo a b, (t * χ t) •
        (∫ w : Circle₁, H w • sliceFun u t w ∂circleMeasure) := by
  rw [← integral_radial_scalar ha χ H u (integrableOn_polarTest_smul ha hab hχ hc hs hH hu)]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have he : χ ‖z‖ = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hz (hs hm))
  simp only [he, zero_mul, zero_smul]

/-- The angular identity with the polar Jacobian still visible. -/
lemma angular_pairing_weighted {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a b) {H : ℂ → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    {u : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (hw : TauCeti.HasWeakFDerivOn volume (annulusOpens a b) u U)
    (hu : MemLp u 2 (volume.restrict (annulusSet a b)))
    (h1 : MemLp (fun z => U z 1) 2 (volume.restrict (annulusSet a b)))
    (hI : MemLp (fun z => U z Complex.I) 2 (volume.restrict (annulusSet a b))) :
    (∫ t in Ioo a b, (t * χ t) •
      (∫ w : Circle₁, angularTestDeriv H w • sliceFun u t w ∂circleMeasure)) =
      -∫ t in Ioo a b, (t * χ t) •
        (∫ w : Circle₁, H w • sliceFun (angularField U) t w ∂circleMeasure) := by
  let ψ : 𝓓(annulusOpens a b, ℝ) :=
    ⟨polarTest χ H, contDiff_polarTest ha hχ hs hH, hasCompactSupport_polarTest hc H,
      tsupport_polarTest_subset.trans (fun _ hz => hs hz)⟩
  have hid := weak_angular_generator hw ψ
  change (∫ z, fderiv ℝ (polarTest χ H) z (z * Complex.I) • u z) =
    -∫ z, polarTest χ H z • angularField U z at hid
  simp_rw [polarTest_rotation ha hχ hs hH] at hid
  rw [integral_polarTest_smul ha hab hχ hc hs (contDiff_angularTestDeriv hH) hu,
    integral_polarTest_smul ha hab hχ hc hs hH (memLp_angularField h1 hI)] at hid
  exact hid

/-- Using χ/r cancels the Jacobian without changing the angular differentiation. -/
theorem angular_pairing_identity {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a b) {H : ℂ → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    {u : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (hw : TauCeti.HasWeakFDerivOn volume (annulusOpens a b) u U)
    (hu : MemLp u 2 (volume.restrict (annulusSet a b)))
    (h1 : MemLp (fun z => U z 1) 2 (volume.restrict (annulusSet a b)))
    (hI : MemLp (fun z => U z Complex.I) 2 (volume.restrict (annulusSet a b))) :
    (∫ t in Ioo a b, χ t •
      (∫ w : Circle₁, angularTestDeriv H w • sliceFun u t w ∂circleMeasure)) =
      -∫ t in Ioo a b, χ t •
        (∫ w : Circle₁, H w • sliceFun (angularField U) t w ∂circleMeasure) := by
  have hid := angular_pairing_weighted ha hab (contDiff_radialProfile ha hχ hs)
    (hasCompactSupport_radialProfile hc) (tsupport_radialProfile_subset hs) hH hw hu h1 hI
  have he (t : ℝ) : t * radialProfile χ t = χ t := congrFun (radialProfile_smul ha hs) t
  simpa only [he] using hid

end KsIndex.Trace
