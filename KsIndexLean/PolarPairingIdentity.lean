module

public import KsIndexLean.PolarPairingPreparation

@[expose] public section


open Set MeasureTheory
open scoped ContDiff

namespace KsIndex.Trace

/-- Fubini on the proved polar factorization, with the Jacobian explicit. -/
lemma integral_radial_scalar {a b : ℝ} (ha : 0 < a)
    (S : ℝ → ℝ) (H : ℂ → ℝ) (u : ℂ → ℂ)
    (hf : IntegrableOn (fun z => (S ‖z‖ * angExt H z) • u z)
      (annulusSet a b) volume) :
    (∫ z in annulusSet a b, (S ‖z‖ * angExt H z) • u z) =
      ∫ t in Ioo a b, (t * S t) • (∫ w : Circle₁, H w • sliceFun u t w ∂circleMeasure) := by
  rw [integral_annulus_eq_weighted ha hf.aestronglyMeasurable,
    MeasureTheory.integral_prod _ (integrable_weighted_pullback ha hf)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have ht0 : 0 < t := lt_trans ha ht.1
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with w
  have hn : ‖t • (w : ℂ)‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0,
      mem_sphere_zero_iff_norm.mp w.property, mul_one]
  simp only [polarMul, hn, angExt, nUnit_of_circle t ht0, sliceFun, smul_smul]
  congr 1
  ring

/-- The scalar weak radial identity after removing the Jacobian by χ/r. -/
theorem radial_pairing_identity {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo a b) {H : ℂ → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    {u : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (hw : TauCeti.HasWeakFDerivOn volume (annulusOpens a b) u U)
    (hu : MemLp u 2 (volume.restrict (annulusSet a b)))
    (h1 : MemLp (fun z => U z 1) 2 (volume.restrict (annulusSet a b)))
    (hI : MemLp (fun z => U z Complex.I) 2 (volume.restrict (annulusSet a b))) :
    (∫ t in Ioo a b, deriv χ t • (∫ w : Circle₁, H w • sliceFun u t w ∂circleMeasure)) =
      -∫ t in Ioo a b, χ t •
        (∫ w : Circle₁, H w • sliceFun (radialField U) t w ∂circleMeasure) := by
  let φ := radialProfile χ
  have hφ := contDiff_radialProfile ha hχ hχs
  have hφs := tsupport_radialProfile_subset hχs
  have hid := weak_radial_identity ha hw hφ (hasCompactSupport_radialProfile hχc) hφs hH
  have hz (z : ℂ) (hz : z ∉ annulusSet a b) : φ ‖z‖ = 0 ∧ deriv φ ‖z‖ = 0 := by
    have hn : ‖z‖ ∉ tsupport φ := fun h => hz (hφs h)
    exact ⟨image_eq_zero_of_notMem_tsupport hn, deriv_eq_zero_of_notMem_tsupport hn⟩
  have hl : (∫ z in annulusSet a b, ((deriv φ ‖z‖ + φ ‖z‖ * ‖z‖⁻¹) * angExt H z) • u z) =
      ∫ z, ((deriv φ ‖z‖ + φ ‖z‖ * ‖z‖⁻¹) * angExt H z) • u z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz'
    simp [(hz z hz').1, (hz z hz').2]
  have hr : (∫ z in annulusSet a b, (φ ‖z‖ * angExt H z) • radialField U z) =
      ∫ z, (φ ‖z‖ * angExt H z) • radialField U z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz'
    simp [(hz z hz').1]
  rw [← hl, ← hr] at hid
  have hi := integrableOn_radial_pairing_fields ha hab hχ hχc hχs hH hu h1 hI
  rw [integral_radial_scalar ha (fun t => deriv φ t + φ t * t⁻¹) H u hi.1,
    integral_radial_scalar ha φ H (radialField U) hi.2] at hid
  have hlw : (∫ t in Ioo a b, (t * (deriv φ t + φ t * t⁻¹)) •
      (∫ w : Circle₁, H w • sliceFun u t w ∂circleMeasure)) =
      ∫ t in Ioo a b, deriv χ t • (∫ w : Circle₁, H w • sliceFun u t w ∂circleMeasure) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans ha ht.1)
    have he : t * (deriv φ t + φ t * t⁻¹) = deriv χ t := by
      rw [← radialProfile_weight ha hχ hχs t]
      dsimp [φ]
      field_simp
    rw [he]
  rw [hlw] at hid
  have he (t : ℝ) : t * φ t = χ t := congrFun (radialProfile_smul ha hχs) t
  simpa only [he] using hid

end KsIndex.Trace
