module

public import KsIndexLean.CircleMeasure
public import KsIndexLean.EndpointRepresentative

@[expose] public section


/-! The same-sign boundary pullback h(w) ↦ h(exp(iθ)w) is a complex-linear
isometry. Endpoint naturality below is conditional on weak identities and a.e.
radial compatibility; it does not assert a two-dimensional weak chain rule. -/

open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace

lemma circleRotate_zero (w : Circle₁) : circleRotate 0 w = w := by
  apply Subtype.ext
  simp [circleRotate]

lemma circleRotate_add (α β : ℝ) (w : Circle₁) :
    circleRotate (α + β) w = circleRotate α (circleRotate β w) := by
  apply Subtype.ext
  simp [circleRotate, add_mul, Complex.exp_add, mul_assoc]

/-- Same-sign pullback on the actual arclength L² space (mass 2π). -/
def boundaryRotation (θ : ℝ) :
    Lp ℂ 2 circleMeasure →ₗᵢ[ℂ] Lp ℂ 2 circleMeasure :=
  Lp.compMeasurePreservingₗᵢ ℂ (circleRotate θ) (measurePreserving_circleRotate θ)

lemma boundaryRotation_coe_ae (θ : ℝ) (f : Lp ℂ 2 circleMeasure) :
    (boundaryRotation θ f : Circle₁ → ℂ) =ᵐ[circleMeasure] f ∘ circleRotate θ :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_circleRotate θ)

lemma boundaryRotation_norm (θ : ℝ) (f : Lp ℂ 2 circleMeasure) :
    ‖boundaryRotation θ f‖ = ‖f‖ := (boundaryRotation θ).norm_map f

lemma boundaryRotation_zero (f : Lp ℂ 2 circleMeasure) : boundaryRotation 0 f = f := by
  change Lp.compMeasurePreserving (circleRotate 0) _ f = f
  have h : circleRotate 0 = id := funext circleRotate_zero
  simp only [h, Lp.compMeasurePreserving_id_apply]

lemma boundaryRotation_add (α β : ℝ) (f : Lp ℂ 2 circleMeasure) :
    boundaryRotation (α + β) f = boundaryRotation α (boundaryRotation β f) := by
  change Lp.compMeasurePreserving (circleRotate (α + β)) _ f =
    Lp.compMeasurePreserving (circleRotate α) _
      (Lp.compMeasurePreserving (circleRotate β) _ f)
  have h : circleRotate (α + β) = circleRotate β ∘ circleRotate α := by
    funext w
    rw [add_comm, circleRotate_add]
    rfl
  simpa only [h] using Lp.compMeasurePreserving_comp_apply f
    (measurePreserving_circleRotate β) (measurePreserving_circleRotate α)

/-- Inverse rotation recovers the original class, so the action is onto. -/
lemma boundaryRotation_neg (θ : ℝ) (f : Lp ℂ 2 circleMeasure) :
    boundaryRotation (-θ) (boundaryRotation θ f) = f := by
  rw [← boundaryRotation_add, neg_add_cancel, boundaryRotation_zero]

/-- Naturality of the continuous representative under a continuous linear map,
assuming the transported weak data and their a.e. compatibility have been established. -/
theorem representative_map_of_ae
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {a b : ℝ} (hab : a < b) (A : E →L[ℝ] F) {f g : ℝ → E} {f' g' : ℝ → F}
    (hw : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f g 1)
    (hg : IntervalIntegrable g volume a b)
    (hw' : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f' g' 1)
    (hg' : IntervalIntegrable g' volume a b)
    (hf : (fun t => A (f t)) =ᵐ[volume.restrict (Ioo a b)] f')
    {t : ℝ} (ht : t ∈ Icc a b) :
    representative hab f' g' t = A (representative hab f g t) := by
  have hrep := representative_ae_eq hab hw hg
  have hae : (fun t => A (representative hab f g t)) =ᵐ[volume.restrict (Ioo a b)] f' := by
    filter_upwards [hrep, hf] with s hs hs'
    rw [← hs]
    exact hs'
  exact (representative_unique hab hw' hg'
    (A.continuous.comp_continuousOn (representative_continuousOn hab f hg)) hae ht).symm

/-- Boundary rotation commutes with the endpoint once the actual radial
profiles have been shown compatible. Both weak identities remain explicit. -/
theorem representative_boundaryRotation {a b : ℝ} (hab : a < b) (θ : ℝ)
    {f g f' g' : ℝ → Lp ℂ 2 circleMeasure}
    (hw : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f g 1)
    (hg : IntervalIntegrable g volume a b)
    (hw' : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f' g' 1)
    (hg' : IntervalIntegrable g' volume a b)
    (hf : (fun t => boundaryRotation θ (f t)) =ᵐ[volume.restrict (Ioo a b)] f') :
    representative hab f' g' b = boundaryRotation θ (representative hab f g b) :=
  representative_map_of_ae hab ((boundaryRotation θ).toContinuousLinearMap.restrictScalars ℝ)
    hw hg hw' hg' hf ⟨hab.le, le_rfl⟩

end KsIndex.Trace
