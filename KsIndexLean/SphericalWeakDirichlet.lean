module

public import KsIndexLean.SphericalComplexGradient

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.WeakH1

/-- Tangential real/imaginary gradients from the adopted carrier's weak coordinate jet. -/
def weakTangentGradient (u : ComplexH1) (z : ℂ) : Ambient × Ambient :=
  complexGradientLift z (dxCLM u z) (dyCLM u z)

lemma weakTangentGradient_tangent (u : ComplexH1) (z : ℂ) :
    inner ℝ (stereoPoint z) (weakTangentGradient u z).1 = 0 ∧
      inner ℝ (stereoPoint z) (weakTangentGradient u z).2 = 0 := by
  simp [weakTangentGradient, complexGradientLift, gradientLift_tangent]

/-- Representation of the carrier's genuine weak derivative, almost everywhere. -/
lemma weakTangentGradient_represents (u : ComplexH1) :
    ∀ᵐ z ∂volume.restrict (disk : Set ℂ), ∀ w : ℂ,
      (inner ℝ (weakTangentGradient u z).1 (fderiv ℝ stereoPoint z w) : ℂ) +
        Complex.I * (inner ℝ (weakTangentGradient u z).2
          (fderiv ℝ stereoPoint z w) : ℂ) = weakDerivative u z w := by
  filter_upwards [weakDerivative_coordinates u] with z hz
  intro w
  rw [hz]
  exact complexGradientLift_represents z (dxCLM u z) (dyCLM u z) w

lemma weakTangentGradient_pair_cancel (u v : ComplexH1) (z : ℂ) :
    (stereoAreaDensity z : ℂ) * tangentPair (weakTangentGradient u z)
      (weakTangentGradient v z) = (starRingEnd ℂ) (dxCLM u z) * dxCLM v z +
        (starRingEnd ℂ) (dyCLM u z) * dyCLM v z :=
  complexGradientLift_pair_cancel z _ _ _ _

lemma integrable_weakTangent_pair (u v : ComplexH1) :
    Integrable (fun z => (stereoAreaDensity z : ℂ) *
      tangentPair (weakTangentGradient u z) (weakTangentGradient v z))
        (volume.restrict (disk : Set ℂ)) := by
  have he : (fun z => (stereoAreaDensity z : ℂ) *
      tangentPair (weakTangentGradient u z) (weakTangentGradient v z)) =
      fun z => (starRingEnd ℂ) (dxCLM u z) * dxCLM v z +
        (starRingEnd ℂ) (dyCLM u z) * dyCLM v z := by
    funext z
    exact weakTangentGradient_pair_cancel u v z
  rw [he]
  exact dirichlet_integrable u v

/-- The weak Hermitian Dirichlet form equals the tangent-gradient chart integral. -/
theorem dirichlet_eq_tangent_chart (u v : ComplexH1) :
    dirichlet u v = ∫ z in (disk : Set ℂ), (stereoAreaDensity z : ℂ) *
      tangentPair (weakTangentGradient u z) (weakTangentGradient v z) := by
  rw [dirichlet_integral]
  apply integral_congr_ae
  filter_upwards with z
  exact (weakTangentGradient_pair_cancel u v z).symm

end KsIndex.Spherical
