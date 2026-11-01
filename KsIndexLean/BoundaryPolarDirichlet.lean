module

public import KsIndexLean.BoundaryPolarWeights

@[expose] public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- The full weak disk Dirichlet pairing reduces to the radial and angular mode terms. -/
lemma weakDirichlet_boundaryPolarTest_modes {a c : ℝ}
    (ha : 0 < a) (hab : a < 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a c) (n : ℤ) (u : ComplexH1) :
    dirichlet u (compactPolarTestH1 ha hχ hs n) =
      (∫ r in Ioo a 1, (r * deriv χ r : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (interiorDiskRadialMode a 1 u n r))) +
      ∫ r in Ioo a 1, (χ r / r : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (n : ℂ)^2 *
          (starRingEnd ℂ) (interiorDiskMode hab u n r)) := by
  let R := fun z : ℂ => (starRingEnd ℂ) (radialField (Dxy (dxLp u) (dyLp u)) z) *
    (((deriv χ ‖z‖ : ℝ) : ℂ) * fourierAmbient n (nUnit z))
  let T := fun z : ℂ => (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) *
    (starRingEnd ℂ) (angularField (Dxy (dxLp u) (dyLp u)) z) *
    ((n : ℂ) * Complex.I * compactPolarTest χ n z)
  have hm : MemLp (radialField (Dxy (dxLp u) (dyLp u))) 2
      (volume.restrict (annulusSet a 1)) := by
    apply memLp_radialField ha
    · simpa using interiorAnnulus_memLp le_rfl (dxLp u)
    · simpa using interiorAnnulus_memLp le_rfl (dyLp u)
  have hR : IntegrableOn R (annulusSet a 1) volume := by
    have h := integrableOn_boundaryPolarTest_mul ha hab
      (contDiff_infty_iff_deriv.mp hχ).2 hc.deriv (tsupport_deriv_subset.trans hs) n hm.star
    apply h.congr
    filter_upwards [] with z
    dsimp only [R, compactPolarTest]
    change ((deriv χ ‖z‖ : ℝ) : ℂ) * fourierAmbient n (nUnit z) *
      (starRingEnd ℂ) (radialField (Dxy (dxLp u) (dyLp u)) z) = _
    ring
  have hT : IntegrableOn T (annulusSet a 1) volume := by
    have hp := contDiff_radialProfile ha hχ hs
    have hps := tsupport_radialProfile_subset hs
    have h := (integrableOn_boundaryPolarTest_mul ha hab
      (contDiff_radialProfile ha hp hps)
      (hasCompactSupport_radialProfile (hasCompactSupport_radialProfile hc))
      (tsupport_radialProfile_subset hps) n (interiorDiskAngularField_memLp le_rfl u).star).const_mul
        ((n : ℂ) * Complex.I)
    apply h.congr
    filter_upwards [] with z
    dsimp only [T]
    change ((n : ℂ) * Complex.I) *
      (compactPolarTest (radialProfile (radialProfile χ)) n z *
        (starRingEnd ℂ) (angularField (Dxy (dxLp u) (dyLp u)) z)) = _
    rw [compactPolarTest_radialProfile_twice]
    ring
  have hzero : ∀ z ∈ (disk : Set ℂ) \ annulusSet a 1, R z + T z = 0 := by
    intro z hz
    have hd : ‖z‖ < 1 := by
      have hball : z ∈ Metric.ball (0 : ℂ) 1 := hz.1
      simpa only [Metric.mem_ball, dist_zero_right] using hball
    have hn : ‖z‖ ∉ tsupport χ := fun h => hz.2 ⟨(hs h).1, hd⟩
    dsimp only [R, T, compactPolarTest]
    rw [deriv_eq_zero_of_notMem_tsupport hn, image_eq_zero_of_notMem_tsupport hn]
    simp
  rw [weakDirichlet_compactPolarTest ha hχ hs n u]
  have he : (∫ z in (disk : Set ℂ), R z + T z) = ∫ z in annulusSet a 1, R z + T z :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero disk.isOpen.measurableSet
      (interiorAnnulus_subset_disk le_rfl) hzero
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_inv]
  change (∫ z in (disk : Set ℂ), R z + T z) = _
  rw [he, integral_add hR hT]
  exact congrArg₂ (· + ·) (integral_annulus_boundaryPolarTest_radial_deriv ha hab le_rfl hχ hc hs n u)
    (integral_annulus_boundaryPolarTest_angular_weighted ha hab le_rfl hχ hc hs n u)

end KsIndex.Trace
