module

public import KsIndexLean.WeakLinearTransport
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section


/-! Plane rotation preserves volume and open annuli. Local integrability is
transported through compact sets, discharging the analytic inputs to the generic
weak chain rule. No Sobolev quotient carrier or trace operator is defined here. -/

open Set MeasureTheory TopologicalSpace

noncomputable section
namespace KsIndex.Trace

/-- Plane rotation with the same positive-angle convention as circle pullback. -/
def planeRotation (θ : ℝ) : ℂ ≃ₗᵢ[ℝ] ℂ := _root_.rotation (Circle.exp θ)

lemma planeRotation_apply (θ : ℝ) (z : ℂ) :
    planeRotation θ z = Complex.exp (θ * Complex.I) * z := rfl

lemma measurePreserving_planeRotation (θ : ℝ) :
    MeasurePreserving (planeRotation θ) volume volume := (planeRotation θ).measurePreserving

/-- Open annuli, allowing arbitrary real inner and outer radii. -/
def rotationAnnulus (a b : ℝ) : Opens ℂ :=
  ⟨{z | a < ‖z‖ ∧ ‖z‖ < b}, isOpen_lt continuous_const continuous_norm |>.inter
    (isOpen_lt continuous_norm continuous_const)⟩

lemma planeRotation_mem_annulus (θ a b : ℝ) (z : ℂ) :
    z ∈ rotationAnnulus a b ↔ planeRotation θ z ∈ rotationAnnulus a b := by
  change (a < ‖z‖ ∧ ‖z‖ < b) ↔ (a < ‖planeRotation θ z‖ ∧ ‖planeRotation θ z‖ < b)
  rw [(planeRotation θ).norm_map]

/-- A measure-preserving linear equivalence transports local integrability
on open sets, provided its domain is locally compact. -/
theorem locallyIntegrableOn_linear_pullback
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [LocallyCompactSpace E]
    [NormedAddCommGroup F] {μ : Measure E} {Ω Ω' : Opens E}
    (e : E ≃L[ℝ] E) (he : MeasurePreserving e μ μ)
    (hΩ : ∀ x, x ∈ Ω' ↔ e x ∈ Ω) {u : E → F}
    (hu : LocallyIntegrableOn u Ω μ) : LocallyIntegrableOn (u ∘ e) Ω' μ := by
  apply (locallyIntegrableOn_iff Ω'.isOpen.isLocallyClosed).mpr
  intro k hk hkc
  have hi : IntegrableOn u (e '' k) μ := hu.integrableOn_compact_subset
    (by rintro _ ⟨x, hx, rfl⟩; exact (hΩ x).mp (hk hx)) (hkc.image e.continuous)
  exact ((he.restrict_image_emb e.toHomeomorph.measurableEmbedding k).integrable_comp_emb
    e.toHomeomorph.measurableEmbedding).mpr hi

/-- Weak Frechet rotation chain rule on the open annulus; local integrability
is proved from the original weak predicate, not assumed for the rotated data. -/
theorem weakFDeriv_planeRotation (θ a b : ℝ)
    {u : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (hw : TauCeti.HasWeakFDerivOn volume (rotationAnnulus a b) u U) :
    TauCeti.HasWeakFDerivOn volume (rotationAnnulus a b)
      (u ∘ planeRotation θ)
      (fun z => (U (planeRotation θ z)).comp
        (planeRotation θ).toContinuousLinearEquiv.toContinuousLinearMap) := by
  let e := (planeRotation θ).toContinuousLinearEquiv
  have he : MeasurePreserving e volume volume := measurePreserving_planeRotation θ
  have hΩ : ∀ z, z ∈ rotationAnnulus a b ↔ e z ∈ rotationAnnulus a b :=
    planeRotation_mem_annulus θ a b
  apply weakFDeriv_linear_transport e he hΩ hw
  · exact locallyIntegrableOn_linear_pullback e he hΩ (hw.hasWeakLineDerivOn 0).locallyIntegrableOn
  · intro v
    exact locallyIntegrableOn_linear_pullback e he hΩ (hw.hasWeakLineDerivOn (e v)).locallyIntegrableOn_deriv

end KsIndex.Trace
