module

public import KsIndexLean.CircleSobolevL2
public import KsIndexLean.BoundaryRestriction

@[expose] public section


/-! Closed arc-vanishing spaces inside global circle Sobolev spaces.
For nonnegative Sobolev orders, restriction is taken in circle `L²`.
The kernel consists of functions vanishing almost everywhere on the specified
set, with its norm inherited from the global Sobolev space.
-/
noncomputable section
open MeasureTheory Set
namespace KsIndex.CircleSobolev
open KsIndex.Trace

def arcRestriction {s : ℝ} (hs : 0 ≤ s) (A : Set Circle₁) :
    Space s →L[ℂ] Lp ℂ 2 (circleMeasure.restrict A) :=
  (boundaryRestrictCLM A).comp (toL2 hs)

/-- The closed subspace whose L² realization vanishes almost everywhere on `A`. -/
def arcZero {s : ℝ} (hs : 0 ≤ s) (A : Set Circle₁) : Submodule ℂ (Space s) :=
  (arcRestriction hs A).ker

theorem isClosed_arcZero {s : ℝ} (hs : 0 ≤ s) (A : Set Circle₁) :
    IsClosed (arcZero hs A : Set (Space s)) := (arcRestriction hs A).isClosed_ker

theorem mem_arcZero_iff {s : ℝ} (hs : 0 ≤ s) (A : Set Circle₁) (u : Space s) :
    u ∈ arcZero hs A ↔ (toL2 hs u : Circle₁ → ℂ) =ᵐ[circleMeasure.restrict A] 0 := by
  change boundaryRestrict A (toL2 hs u) = 0 ↔ _
  constructor
  · intro h
    have he := boundaryRestrict_coe_ae A (toL2 hs u)
    rw [h] at he
    exact he.symm.trans (Lp.coeFn_zero ℂ 2 (circleMeasure.restrict A))
  · intro h
    apply Lp.ext
    exact ((boundaryRestrict_coe_ae A (toL2 hs u)).trans h).trans
      (Lp.coeFn_zero ℂ 2 (circleMeasure.restrict A)).symm

theorem mem_arcZero_iff_norm {s : ℝ} (hs : 0 ≤ s) (A : Set Circle₁) (u : Space s) :
    u ∈ arcZero hs A ↔ ‖arcRestriction hs A u‖ = 0 := by
  change arcRestriction hs A u = 0 ↔ _
  exact norm_eq_zero.symm

end KsIndex.CircleSobolev
