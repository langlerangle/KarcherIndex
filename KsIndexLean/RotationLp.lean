module

public import KsIndexLean.PlaneRotation
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

@[expose] public section


/-! Rotation preserves annular Lp values and membership of the two real weak
derivative components. The statements transport functions and weak derivative
data; a bundled H¹ action and its Hilbert graph norm require separate results. -/

open Set MeasureTheory TopologicalSpace

namespace KsIndex.Trace

lemma measurePreserving_planeRotation_annulus (θ a b : ℝ) :
    MeasurePreserving (planeRotation θ)
      (volume.restrict (rotationAnnulus a b : Set ℂ))
      (volume.restrict (rotationAnnulus a b : Set ℂ)) := by
  have hp : planeRotation θ ⁻¹' (rotationAnnulus a b : Set ℂ) = rotationAnnulus a b := by
    ext z
    exact (planeRotation_mem_annulus θ a b z).symm
  simpa only [hp] using (measurePreserving_planeRotation θ).restrict_preimage
    (rotationAnnulus a b).isOpen.measurableSet

lemma memLp_planeRotation {F : Type*} [NormedAddCommGroup F]
    (θ a b : ℝ) {p : ENNReal} {u : ℂ → F}
    (hu : MemLp u p (volume.restrict (rotationAnnulus a b : Set ℂ))) :
    MemLp (u ∘ planeRotation θ) p (volume.restrict (rotationAnnulus a b : Set ℂ)) :=
  hu.comp_measurePreserving (measurePreserving_planeRotation_annulus θ a b)

lemma eLpNorm_planeRotation {F : Type*} [NormedAddCommGroup F]
    (θ a b : ℝ) {p : ENNReal} {u : ℂ → F}
    (hu : AEStronglyMeasurable u (volume.restrict (rotationAnnulus a b : Set ℂ))) :
    eLpNorm (u ∘ planeRotation θ) p (volume.restrict (rotationAnnulus a b : Set ℂ)) =
      eLpNorm u p (volume.restrict (rotationAnnulus a b : Set ℂ)) :=
  eLpNorm_comp_measurePreserving hu (measurePreserving_planeRotation_annulus θ a b)

/-- Lp control in the two real coordinate directions controls every fixed direction. -/
lemma memLp_linear_direction {μ : Measure ℂ} {p : ENNReal}
    {U : ℂ → ℂ →L[ℝ] ℂ}
    (h1 : MemLp (fun z => U z 1) p μ) (hI : MemLp (fun z => U z Complex.I) p μ)
    (v : ℂ) : MemLp (fun z => U z v) p μ := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    simp
  have heq : (fun z => U z v) =
      (fun z => v.re • U z 1 + v.im • U z Complex.I) := by
    funext z
    conv_lhs => rw [hv]
    simp only [map_add, map_smul]
  rw [heq]
  exact (h1.const_smul v.re).add (hI.const_smul v.im)

lemma memLp_rotated_derivative (θ a b : ℝ) {p : ENNReal}
    {U : ℂ → ℂ →L[ℝ] ℂ}
    (h1 : MemLp (fun z => U z 1) p (volume.restrict (rotationAnnulus a b : Set ℂ)))
    (hI : MemLp (fun z => U z Complex.I) p
      (volume.restrict (rotationAnnulus a b : Set ℂ))) (v : ℂ) :
    MemLp (fun z => U (planeRotation θ z) (planeRotation θ v)) p
      (volume.restrict (rotationAnnulus a b : Set ℂ)) :=
  memLp_planeRotation θ a b (memLp_linear_direction h1 hI (planeRotation θ v))

/-- Original weak data with L² value and two L² derivative components remain
such data after rotation. All transformed analytic hypotheses are derived. -/
theorem weakL2Data_planeRotation (θ a b : ℝ) {u : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (hw : TauCeti.HasWeakFDerivOn volume (rotationAnnulus a b) u U)
    (hu : MemLp u 2 (volume.restrict (rotationAnnulus a b : Set ℂ)))
    (h1 : MemLp (fun z => U z 1) 2 (volume.restrict (rotationAnnulus a b : Set ℂ)))
    (hI : MemLp (fun z => U z Complex.I) 2
      (volume.restrict (rotationAnnulus a b : Set ℂ))) :
    TauCeti.HasWeakFDerivOn volume (rotationAnnulus a b) (u ∘ planeRotation θ)
      (fun z => (U (planeRotation θ z)).comp
        (planeRotation θ).toContinuousLinearEquiv.toContinuousLinearMap) ∧
    MemLp (u ∘ planeRotation θ) 2 (volume.restrict (rotationAnnulus a b : Set ℂ)) ∧
    ∀ v, MemLp (fun z => U (planeRotation θ z) (planeRotation θ v)) 2
      (volume.restrict (rotationAnnulus a b : Set ℂ)) :=
  ⟨weakFDeriv_planeRotation θ a b hw, memLp_planeRotation θ a b hu,
    memLp_rotated_derivative θ a b h1 hI⟩

end KsIndex.Trace
