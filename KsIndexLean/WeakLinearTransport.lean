module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Equiv

@[expose] public section


/-! Weak change of variables under a measure-preserving real linear equivalence.
Local integrability of the pulled-back data is explicit; this module proves the
test-function identity, not an H¹ carrier or its norm preservation. -/

open Set MeasureTheory TopologicalSpace
open scoped ContDiff

namespace KsIndex.Trace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The inverse-pulled test derivative transforms in the forward direction. -/
lemma lineDeriv_inverse_linear (e : E ≃L[ℝ] E) {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x v : E) :
    lineDeriv ℝ (φ ∘ e.symm) (e x) (e v) = lineDeriv ℝ φ x v := by
  have hd := (hφ.differentiable (by simp)).differentiableAt (x := x)
  have hd' := (hφ.differentiable (by simp)).differentiableAt (x := e.symm (e x))
  have hh := hd'.hasFDerivAt.comp (e x) e.symm.hasFDerivAt
  rw [hd.lineDeriv_eq_fderiv]
  simpa using (hh.hasLineDerivAt (e v)).lineDeriv

/-- Directional weak chain rule. The source domain is the preimage of Ω;
transformed local integrability is required independently of the weak identity. -/
theorem weakLineDeriv_linear_transport {μ : Measure E} {Ω Ω' : Opens E}
    (e : E ≃L[ℝ] E) (he : MeasurePreserving e μ μ)
    (hΩ : ∀ x, x ∈ Ω' ↔ e x ∈ Ω) {u u' : E → F} {v : E}
    (hw : TauCeti.HasWeakLineDerivOn μ Ω u u' (e v))
    (hu : LocallyIntegrableOn (u ∘ e) Ω' μ)
    (hu' : LocallyIntegrableOn (u' ∘ e) Ω' μ) :
    TauCeti.HasWeakLineDerivOn μ Ω' (u ∘ e) (u' ∘ e) v := by
  apply (TauCeti.hasWeakLineDerivOn_iff hu hu').mpr
  intro φ hφ hc hs
  have hψ : ContDiff ℝ ∞ (φ ∘ e.symm) := hφ.comp e.symm.contDiff
  have hcψ : HasCompactSupport (φ ∘ e.symm) := hc.comp_homeomorph e.symm.toHomeomorph
  have hsψ : tsupport (φ ∘ e.symm) ⊆ Ω := by
    intro y hy
    have hpre : e.symm y ∈ tsupport φ :=
      tsupport_comp_subset_preimage φ e.symm.continuous hy
    simpa using (hΩ (e.symm y)).mp (hs hpre)
  have hid := (TauCeti.hasWeakLineDerivOn_iff hw.locallyIntegrableOn
    hw.locallyIntegrableOn_deriv).mp hw (φ ∘ e.symm) hψ hcψ hsψ
  have hleft := he.integral_comp e.toHomeomorph.measurableEmbedding
    (fun y => lineDeriv ℝ (φ ∘ e.symm) y (e v) • u y)
  have hright := he.integral_comp e.toHomeomorph.measurableEmbedding
    (fun y => (φ ∘ e.symm) y • u' y)
  rw [← hleft, ← hright] at hid
  simpa only [lineDeriv_inverse_linear e hφ, Function.comp_apply,
    e.symm_apply_apply] using hid

/-- The full weak derivative composes with the forward linear map on vectors. -/
theorem weakFDeriv_linear_transport {μ : Measure E} {Ω Ω' : Opens E}
    (e : E ≃L[ℝ] E) (he : MeasurePreserving e μ μ)
    (hΩ : ∀ x, x ∈ Ω' ↔ e x ∈ Ω) {u : E → F} {U : E → E →L[ℝ] F}
    (hw : TauCeti.HasWeakFDerivOn μ Ω u U)
    (hu : LocallyIntegrableOn (u ∘ e) Ω' μ)
    (hU : ∀ v, LocallyIntegrableOn (fun x => U (e x) (e v)) Ω' μ) :
    TauCeti.HasWeakFDerivOn μ Ω' (u ∘ e)
      (fun x => (U (e x)).comp e.toContinuousLinearMap) := by
  apply TauCeti.hasWeakFDerivOn_iff.mpr
  intro v
  exact weakLineDeriv_linear_transport e he hΩ (hw.hasWeakLineDerivOn (e v)) hu (hU v)

end KsIndex.Trace
