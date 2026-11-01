module

public import KsIndexLean.FiniteHilbertFormDomain
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

@[expose] public section


noncomputable section
open Set
namespace KsIndex.Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Coercivity with lower-bound constant one: the real quadratic pairing
dominates the squared norm. -/
def UnitCoercive (A : E →L[ℂ] E) : Prop :=
  ∀ u, ‖u‖ ^ 2 ≤ (inner ℂ (A u) u).re

omit [CompleteSpace E] in
lemma UnitCoercive.norm_le {A : E →L[ℂ] E} (hA : UnitCoercive A) (u : E) :
    ‖u‖ ≤ ‖A u‖ := by
  have hi := (Complex.re_le_norm (inner ℂ (A u) u)).trans (norm_inner_le_norm (A u) u)
  have hc := hA u
  by_cases hu : ‖u‖ = 0
  · rw [hu]; exact norm_nonneg _
  · have hp : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg u) (Ne.symm hu)
    nlinarith

omit [CompleteSpace E] in
lemma UnitCoercive.antilipschitz {A : E →L[ℂ] E} (hA : UnitCoercive A) :
    AntilipschitzWith 1 A :=
  A.antilipschitz_of_bound (by simpa using hA.norm_le)

lemma UnitCoercive.closed_range {A : E →L[ℂ] E} (hA : UnitCoercive A) :
    IsClosed (A.range : Set E) :=
  hA.antilipschitz.isClosed_range A.uniformContinuous

lemma UnitCoercive.range_eq_top {A : E →L[ℂ] E} (hA : UnitCoercive A) :
    A.range = ⊤ := by
  let := hA.closed_range.completeSpace_coe
  rw [← A.range.orthogonal_orthogonal]
  rw [Submodule.eq_top_iff']
  intro v w hw
  have hw0 : w = 0 := by
    have hi : inner ℂ (A w) w = 0 := hw _ ⟨w, rfl⟩
    have hc := hA w
    rw [hi, Complex.zero_re] at hc
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg w])
  rw [hw0]
  exact inner_zero_left _

/-- Complex-linear bounded inverse, without a realification or multiplicity change. -/
def UnitCoercive.equiv {A : E →L[ℂ] E} (hA : UnitCoercive A) : E ≃L[ℂ] E :=
  ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hA.antilipschitz.injective) hA.range_eq_top

lemma UnitCoercive.equiv_apply {A : E →L[ℂ] E} (hA : UnitCoercive A) (u : E) :
    hA.equiv u = A u := rfl

lemma UnitCoercive.inverse_norm_le {A : E →L[ℂ] E} (hA : UnitCoercive A) (f : E) :
    ‖hA.equiv.symm f‖ ≤ ‖f‖ := by
  have h := hA.norm_le (hA.equiv.symm f)
  simpa only [← hA.equiv_apply, ContinuousLinearEquiv.apply_symm_apply] using h

/-- Riesz realization of a normalized coercive complex sesquilinear form. -/
def coerciveFormEquiv (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) : E ≃L[ℂ] E :=
  UnitCoercive.equiv (A := InnerProductSpace.continuousLinearMapOfBilin B)
    (fun u => by simpa only [InnerProductSpace.continuousLinearMapOfBilin_apply] using hB u)

lemma coerciveFormEquiv_weak (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (f v : E) :
    B ((coerciveFormEquiv B hB).symm f) v = inner ℂ f v := by
  rw [← InnerProductSpace.continuousLinearMapOfBilin_apply]
  change inner ℂ (coerciveFormEquiv B hB ((coerciveFormEquiv B hB).symm f)) v = _
  rw [ContinuousLinearEquiv.apply_symm_apply]

end KsIndex.Spectral
