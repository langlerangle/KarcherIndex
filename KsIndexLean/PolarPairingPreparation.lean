module

public import KsIndexLean.PolarPullback

@[expose] public section


/-! Integrability for the two scalar-weighted fields in the weak radial pairing
argument. The actual boundedness and L² inputs establish Bochner integrability
before change of variables or Fubini. -/

open Set MeasureTheory
open scoped ContDiff

namespace KsIndex.Trace

lemma continuousOn_angExt_annulus {a b : ℝ} (ha : 0 < a) {H : ℂ → ℝ}
    (hH : Continuous H) : ContinuousOn (angExt H) (annulusSet a b) := by
  have hinv : ContinuousOn (fun z : ℂ => ‖z‖⁻¹) (annulusSet a b) :=
    continuous_norm.continuousOn.inv₀ (fun z hz =>
      ne_of_gt (lt_trans ha (mem_annulusSet.mp hz).1))
  exact hH.comp_continuousOn (hinv.smul continuous_id.continuousOn)

lemma continuousOn_radial_pairing_scalars {a b : ℝ} (ha : 0 < a)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : tsupport χ ⊆ Ioo a b)
    {H : ℂ → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H) :
    ContinuousOn (fun z : ℂ =>
      (deriv (radialProfile χ) ‖z‖ + radialProfile χ ‖z‖ * ‖z‖⁻¹) * angExt H z)
      (annulusSet a b) ∧
    ContinuousOn (fun z : ℂ => radialProfile χ ‖z‖ * angExt H z)
      (annulusSet a b) := by
  have hφ := contDiff_radialProfile ha hχ hχs
  have hv := hφ.continuous.comp (continuous_norm : Continuous (fun z : ℂ => ‖z‖))
  have hd := (contDiff_infty_iff_deriv.mp hφ).2.continuous.comp
    (continuous_norm : Continuous (fun z : ℂ => ‖z‖))
  have hinv : ContinuousOn (fun z : ℂ => ‖z‖⁻¹) (annulusSet a b) :=
    continuous_norm.continuousOn.inv₀ (fun z hz =>
      ne_of_gt (lt_trans ha (mem_annulusSet.mp hz).1))
  have hh := continuousOn_angExt_annulus (b := b) ha hH.continuous
  exact ⟨(hd.continuousOn.add (hv.continuousOn.mul hinv)).mul hh,
    hv.continuousOn.mul hh⟩

/-- Both planar integrands are genuinely integrable from the original L² data.
These provide the integrability hypotheses for polar change of variables and Fubini. -/
theorem integrableOn_radial_pairing_fields {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo a b) {H : ℂ → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    {u : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet a b)))
    (h1 : MemLp (fun z => U z 1) 2 (volume.restrict (annulusSet a b)))
    (hI : MemLp (fun z => U z Complex.I) 2 (volume.restrict (annulusSet a b))) :
    IntegrableOn (fun z =>
      ((deriv (radialProfile χ) ‖z‖ + radialProfile χ ‖z‖ * ‖z‖⁻¹) * angExt H z) • u z)
      (annulusSet a b) volume ∧
    IntegrableOn (fun z => (radialProfile χ ‖z‖ * angExt H z) • radialField U z)
      (annulusSet a b) volume := by
  obtain ⟨C, hC1, hC2⟩ := scalar_bounds ha hχ hχc hχs hH
  have hs := continuousOn_radial_pairing_scalars ha hχ hχs hH
  exact ⟨integrableOn_bdd_smul ha hab
      (hs.1.aestronglyMeasurable measurableSet_annulusSet) hC1 hu,
    integrableOn_bdd_smul ha hab
      (hs.2.aestronglyMeasurable measurableSet_annulusSet) hC2 (memLp_radialField ha h1 hI)⟩

end KsIndex.Trace
