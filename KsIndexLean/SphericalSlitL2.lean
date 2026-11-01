module

public import KsIndexLean.SphericalWeightedIntegrals
public import KsIndexLean.SphericalSlitDomain

@[expose] public section


open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KsIndex.Spherical

lemma sphereChart_preimage_slitSphere (k : ℕ) :
    sphereChart ⁻¹' (slitSphere k : Set Sphere) = (KsIndex.Bracket.slit k)ᶜ := by
  ext z
  exact sphereChart_mem_slitSphere k z

lemma memL2_slitSphere (k : ℕ) (F : Sphere → ℂ) :
    MemLp F 2 ((volume : Measure Ambient).toSphere.restrict (slitSphere k)) ↔
      MemLp (F ∘ sphereChart) 2 (stereoAreaMeasure.restrict (KsIndex.Bracket.slit k)ᶜ) := by
  rw [memLp_sphere_restrict, sphereChart_preimage_slitSphere]

lemma eL2Norm_slitSphere (k : ℕ) (F : Sphere → ℂ) :
    eLpNorm F 2 ((volume : Measure Ambient).toSphere.restrict (slitSphere k)) =
      eLpNorm (F ∘ sphereChart) 2 (stereoAreaMeasure.restrict (KsIndex.Bracket.slit k)ᶜ) := by
  rw [eLpNorm_sphere_restrict, sphereChart_preimage_slitSphere]

lemma integral_slitSphere_pairing (k : ℕ) (F G : Sphere → ℂ)
    (hF : Measurable F) (hG : Measurable G) :
    ∫ p in slitSphere k, (starRingEnd ℂ) (F p) * G p
      ∂(volume : Measure Ambient).toSphere =
      ∫ z in (KsIndex.Bracket.slit k)ᶜ, (4 / (1 + ‖z‖ ^ 2) ^ 2 : ℝ) •
        ((starRingEnd ℂ) (F (sphereChart z)) * G (sphereChart z)) ∂volume := by
  rw [integral_sphere_pairing _ (slitSphere k).isOpen.measurableSet F G hF hG,
    sphereChart_preimage_slitSphere]

end KsIndex.Spherical
