module

public import KsIndexLean.BoundaryRotation

@[expose] public section


/-! Radial slicing commutes with same-sign rotation. The scalar slice identities
are explicit a.e. inputs, so this module is independent of a chosen polar-profile
construction. The endpoint corollary still requires both weak identities. -/

open Set MeasureTheory

namespace KsIndex.Trace

lemma radial_circleRotate (θ t : ℝ) (w : Circle₁) :
    t • (circleRotate θ w : ℂ) = Complex.exp (θ * Complex.I) * (t • (w : ℂ)) := by
  change t • (Complex.exp (θ * Complex.I) * (w : ℂ)) = _
  exact (mul_smul_comm t (Complex.exp (θ * Complex.I)) (w : ℂ)).symm

/-- A rotated scalar slice determines the pullback of its original L² class. -/
theorem boundaryRotation_eq_of_slices (θ t : ℝ) {u : ℂ → ℂ}
    {f f' : Lp ℂ 2 circleMeasure}
    (hf : (f : Circle₁ → ℂ) =ᵐ[circleMeasure] (fun w => u (t • (w : ℂ))))
    (hf' : (f' : Circle₁ → ℂ) =ᵐ[circleMeasure]
      (fun w => u (Complex.exp (θ * Complex.I) * (t • (w : ℂ))))) :
    boundaryRotation θ f = f' := by
  apply Lp.ext
  have hcomp := (measurePreserving_circleRotate θ).quasiMeasurePreserving.ae_eq_comp hf
  filter_upwards [boundaryRotation_coe_ae θ f, hcomp, hf'] with w hw hc hw'
  calc
    (boundaryRotation θ f : Circle₁ → ℂ) w = f (circleRotate θ w) := hw
    _ = u (t • (circleRotate θ w : ℂ)) := hc
    _ = u (Complex.exp (θ * Complex.I) * (t • (w : ℂ))) := by rw [radial_circleRotate]
    _ = f' w := hw'.symm

/-- Nested a.e. slice identities yield compatibility of the L²-valued profiles.
No regularity of u or point values at exceptional radii are required. -/
theorem radialProfiles_rotation_ae (θ : ℝ) {u : ℂ → ℂ}
    {ν : Measure ℝ} {f f' : ℝ → Lp ℂ 2 circleMeasure}
    (hf : ∀ᵐ t ∂ν, (f t : Circle₁ → ℂ) =ᵐ[circleMeasure]
      (fun w => u (t • (w : ℂ))))
    (hf' : ∀ᵐ t ∂ν, (f' t : Circle₁ → ℂ) =ᵐ[circleMeasure]
      (fun w => u (Complex.exp (θ * Complex.I) * (t • (w : ℂ))))) :
    (fun t => boundaryRotation θ (f t)) =ᵐ[ν] f' := by
  filter_upwards [hf, hf'] with t ht ht'
  exact boundaryRotation_eq_of_slices θ t ht ht'

/-- Endpoint covariance from actual scalar slice identities. The weak identity
for the rotated data must still be supplied by the weak chain-rule argument. -/
theorem representative_rotation_of_slices {a b : ℝ} (hab : a < b) (θ : ℝ)
    {u : ℂ → ℂ} {f g f' g' : ℝ → Lp ℂ 2 circleMeasure}
    (hw : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f g 1)
    (hg : IntervalIntegrable g volume a b)
    (hw' : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f' g' 1)
    (hg' : IntervalIntegrable g' volume a b)
    (hf : ∀ᵐ t ∂volume.restrict (Ioo a b), (f t : Circle₁ → ℂ) =ᵐ[circleMeasure]
      (fun w => u (t • (w : ℂ))))
    (hf' : ∀ᵐ t ∂volume.restrict (Ioo a b), (f' t : Circle₁ → ℂ) =ᵐ[circleMeasure]
      (fun w => u (Complex.exp (θ * Complex.I) * (t • (w : ℂ))))) :
    representative hab f' g' b = boundaryRotation θ (representative hab f g b) :=
  representative_boundaryRotation hab θ hw hg hw' hg' (radialProfiles_rotation_ae θ hf hf')

end KsIndex.Trace
