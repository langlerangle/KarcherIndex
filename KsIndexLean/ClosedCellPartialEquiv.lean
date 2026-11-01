module

public import Mathlib.Topology.CWComplex.Classical.Finite

@[expose] public section


/-! Extending an embedded closed cell to the partial equivalence used by CW complexes. -/
noncomputable section
open Set Metric Topology
namespace KsIndex
variable {n : ℕ} {X : Type*} [TopologicalSpace X]

/-- Extend a closed cell map arbitrarily outside its closed ball. -/
def closedCellExtension (f : closedBall (0 : Fin n → ℝ) 1 → X) (x : Fin n → ℝ) : X := by
  classical
  exact if hx : x ∈ closedBall 0 1 then f ⟨x,hx⟩ else f ⟨0, by simp⟩

omit [TopologicalSpace X] in
lemma closedCellExtension_apply (f : closedBall (0 : Fin n → ℝ) 1 → X)
    (x : closedBall (0 : Fin n → ℝ) 1) : closedCellExtension f x.val = f x := by
  simp only [closedCellExtension, x.property, dite_true]

/-- The inverse coordinate on the image, extended by zero elsewhere. -/
def closedCellInverse (f : closedBall (0 : Fin n → ℝ) 1 → X)
    (hf : IsClosedEmbedding f) (y : X) : Fin n → ℝ := by
  classical
  exact if hy : y ∈ range f then (hf.isEmbedding.toHomeomorph.symm ⟨y,hy⟩).val else 0

lemma closedCellInverse_apply (f : closedBall (0 : Fin n → ℝ) 1 → X)
    (hf : IsClosedEmbedding f) (x : closedBall (0 : Fin n → ℝ) 1) :
    closedCellInverse f hf (f x) = x.val := by
  unfold closedCellInverse
  rw [dite_eq_left (show f x ∈ range f from ⟨x,rfl⟩)]
  change (hf.isEmbedding.toHomeomorph.symm (hf.isEmbedding.toHomeomorph x)).val = x.val
  rw [Homeomorph.symm_apply_apply]

/-- An embedded closed cell determines the standard open-cell partial equivalence. -/
def closedCellPartialEquiv (f : closedBall (0 : Fin n → ℝ) 1 → X)
    (hf : IsClosedEmbedding f) : PartialEquiv (Fin n → ℝ) X where
  toFun := closedCellExtension f
  invFun := closedCellInverse f hf
  source := ball 0 1
  target := f '' {x | x.val ∈ ball 0 1}
  map_source' := by
    intro x hx
    exact ⟨⟨x, ball_subset_closedBall hx⟩, hx, (closedCellExtension_apply f _).symm⟩
  map_target' := by
    rintro y ⟨x,hx,rfl⟩
    rw [closedCellInverse_apply]
    exact hx
  left_inv' := fun x hx => by
    rw [show closedCellExtension f x = f ⟨x,ball_subset_closedBall hx⟩ from
      closedCellExtension_apply f ⟨x,ball_subset_closedBall hx⟩, closedCellInverse_apply f hf]
  right_inv' := by
    rintro y ⟨x,hx,rfl⟩
    rw [closedCellInverse_apply, closedCellExtension_apply]

lemma closedCellExtension_continuousOn (f : closedBall (0 : Fin n → ℝ) 1 → X)
    (hf : Continuous f) : ContinuousOn (closedCellExtension f) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (closedBall (0 : Fin n → ℝ) 1).domRestrict (closedCellExtension f) = f := by
    funext x
    exact closedCellExtension_apply f x
  rw [he]
  exact hf

lemma closedCellInverse_continuousOn (f : closedBall (0 : Fin n → ℝ) 1 → X)
    (hf : IsClosedEmbedding f) : ContinuousOn (closedCellInverse f hf) (range f) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (range f).domRestrict (closedCellInverse f hf) =
      fun y => (hf.isEmbedding.toHomeomorph.symm y).val := by
    funext y
    simp only [Set.domRestrict, closedCellInverse, y.property, dite_true]
  rw [he]
  exact continuous_subtype_val.comp hf.isEmbedding.toHomeomorph.symm.continuous

lemma closedCellPartialEquiv_continuousOn_symm
    (f : closedBall (0 : Fin n → ℝ) 1 → X) (hf : IsClosedEmbedding f) :
    ContinuousOn (closedCellPartialEquiv f hf).symm (closedCellPartialEquiv f hf).target :=
  (closedCellInverse_continuousOn f hf).mono (by rintro y ⟨x,hx,rfl⟩; exact ⟨x,rfl⟩)

omit [TopologicalSpace X] in
lemma closedCellExtension_image (f : closedBall (0 : Fin n → ℝ) 1 → X)
    {S : Set (Fin n → ℝ)} (hS : S ⊆ closedBall 0 1) :
    closedCellExtension f '' S = f '' {x | x.val ∈ S} := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,hS hx⟩, hx, (closedCellExtension_apply f ⟨x,hS hx⟩).symm⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x.val,hx,closedCellExtension_apply f x⟩

lemma closedCellPartialEquiv_closed_image
    (f : closedBall (0 : Fin n → ℝ) 1 → X) (hf : IsClosedEmbedding f) :
    closedCellPartialEquiv f hf '' closedBall 0 1 = range f := by
  change closedCellExtension f '' closedBall 0 1 = _
  rw [closedCellExtension_image f (Subset.refl _)]
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x,rfl⟩
  · rintro ⟨x,rfl⟩
    exact ⟨x,x.property,rfl⟩

end KsIndex
