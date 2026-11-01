module

public import KsIndexLean.SphericalRadialJacobian
public import Mathlib.MeasureTheory.Function.Jacobian

@[expose] public section


open Set MeasureTheory
open scoped ENNReal Pointwise
noncomputable section
namespace KsIndex.Spherical

/-- Genuine three-dimensional change of variables for positive-radius chart sets. -/
theorem lintegral_radialCartesian_image (s : Set (Fin 3 → ℝ))
    (hs : MeasurableSet s) (hpos : s ⊆ {p | 0 < p 0})
    (g : (Fin 3 → ℝ) → ℝ≥0∞) :
    ∫⁻ x in radialCartesian '' s, g x ∂volume =
      ∫⁻ p in s, ENNReal.ofReal
        (p 0 ^ 2 * (4 / (1 + ‖(radialCoord p).2‖ ^ 2) ^ 2)) *
          g (radialCartesian p) ∂volume := by
  have hd : ∀ p ∈ s, HasFDerivWithinAt radialCartesian
      (fderiv ℝ radialCartesian p) s p := by
    intro p _
    have hd := contDiff_radialCartesian.differentiable (by simp)
    exact hd.differentiableAt.hasFDerivAt.hasFDerivWithinAt
  simpa only [abs_det_fderiv_radialCartesian] using
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hd
      (radialCartesian_injOn.mono hpos) g

/-- The image used in the volume formula is exactly the corresponding radial sector. -/
lemma radialCartesian_image_sector (s : Set ℂ) :
    radialCartesian '' (radialCoord ⁻¹' (Ioo (0 : ℝ) 1 ×ˢ s)) =
      Ioo (0 : ℝ) 1 • ((fun z => WithLp.ofLp (stereoPoint z)) '' s) := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(radialCoord p).1, hp.1, WithLp.ofLp (stereoPoint (radialCoord p).2),
      ⟨(radialCoord p).2, hp.2, rfl⟩, rfl⟩
  · rintro ⟨r, hr, w, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨p, hp⟩ := radialCoord_surjective (r, z)
    refine ⟨p, ?_, ?_⟩
    · change radialCoord p ∈ Ioo (0 : ℝ) 1 ×ˢ s
      rw [hp]
      exact ⟨hr, hz⟩
    · simp [radialCartesian, radialStereo, hp]

end KsIndex.Spherical
