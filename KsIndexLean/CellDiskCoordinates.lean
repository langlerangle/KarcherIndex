module

public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section


/-! Coordinates carrying the standard two-cell ball to the complex unit disk. -/
noncomputable section
open Set Metric Topology
namespace KsIndex

/-- A real linear coordinate identification, before adjusting the norms. -/
def cellPlaneLinearEquiv : (Fin 2 → ℝ) ≃L[ℝ] ℂ :=
  (LinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearEquiv.trans Complex.equivRealProdCLM.symm

/-- The adjustment preserves the open ball, closed ball and attaching sphere together. -/
theorem exists_cellDiskCoordinates : ∃ e : (Fin 2 → ℝ) ≃ₜ ℂ,
    e '' ball 0 1 = ball 0 1 ∧ e '' closedBall 0 1 = closedBall 0 1 ∧
      e '' sphere 0 1 = sphere 0 1 := by
  let L := cellPlaneLinearEquiv
  let C := L '' closedBall 0 1
  have hc : Convex ℝ C := (convex_closedBall (0 : Fin 2 → ℝ) 1).linear_image L.toLinearMap
  have hi : interior C = L '' ball 0 1 := by
    rw [show C = L.toHomeomorph '' closedBall 0 1 from rfl,
      ← L.toHomeomorph.image_interior, interior_closedBall _ (by norm_num)]
    rfl
  have hne : (interior C).Nonempty := by
    rw [hi]
    exact ⟨L 0, 0, by simp, rfl⟩
  have hcompact : IsCompact C := (isCompact_closedBall (0 : Fin 2 → ℝ) 1).image L.continuous
  obtain ⟨H, hball, hclosed, hsphere⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hne hcompact.isBounded
  refine ⟨L.toHomeomorph.trans H, ?_, ?_, ?_⟩
  · change (H ∘ L) '' ball 0 1 = _
    rw [Set.image_comp, ← hi]
    exact hball
  · change (H ∘ L) '' closedBall 0 1 = _
    rw [Set.image_comp]
    simpa only [hcompact.isClosed.closure_eq] using hclosed
  · have hf : frontier C = L '' sphere 0 1 := by
      rw [show C = L.toHomeomorph '' closedBall 0 1 from rfl,
        ← L.toHomeomorph.image_frontier, frontier_closedBall _ (by norm_num)]
      rfl
    change (H ∘ L) '' sphere 0 1 = _
    rw [Set.image_comp, ← hf]
    exact hsphere

def cellDiskCoordinates : (Fin 2 → ℝ) ≃ₜ ℂ :=
  Classical.choose exists_cellDiskCoordinates

lemma cellDiskCoordinates_ball : cellDiskCoordinates '' ball 0 1 = ball 0 1 :=
  (Classical.choose_spec exists_cellDiskCoordinates).1

lemma cellDiskCoordinates_closedBall :
    cellDiskCoordinates '' closedBall 0 1 = closedBall 0 1 :=
  (Classical.choose_spec exists_cellDiskCoordinates).2.1

lemma cellDiskCoordinates_sphere : cellDiskCoordinates '' sphere 0 1 = sphere 0 1 :=
  (Classical.choose_spec exists_cellDiskCoordinates).2.2

/-- The standard closed two-cell and the complex closed unit disk are homeomorphic. -/
def cellClosedDiskHomeomorph :
    closedBall (0 : Fin 2 → ℝ) 1 ≃ₜ closedBall (0 : ℂ) 1 :=
  (cellDiskCoordinates.image _).trans (Homeomorph.setCongr cellDiskCoordinates_closedBall)

end KsIndex
