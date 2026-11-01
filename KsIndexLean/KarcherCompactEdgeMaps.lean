module

public import KsIndexLean.KarcherCompactCellMaps
public import KsIndexLean.CellIntervalCoordinates
public import KsIndexLean.ClosedCellPartialEquiv

@[expose] public section


/-! Standard one-cell characteristic maps and two-cell partial equivalences. -/
noncomputable section
open Set Metric Topology
namespace KsIndex.KarcherData.DiskCompactification
open PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

def standardEdgeCoordinates (t : Fin (2 * k)) :
    closedBall (0 : Fin 1 → ℝ) 1 ≃ₜ EdgeInterval k (t.val : ℤ) :=
  cellIntervalCoordinates _ _ (vertexAngle_lt _)

def standardEdgeMap (p : ZMod m × Fin (2 * k)) :
    closedBall (0 : Fin 1 → ℝ) 1 → FilledChain k m :=
  faceEdgeMap (evenCopyIndex p.1) (p.2.val : ℤ) ∘ standardEdgeCoordinates p.2

lemma standardEdgeMap_isClosedEmbedding (p : ZMod m × Fin (2 * k)) :
    IsClosedEmbedding (standardEdgeMap p) :=
  (faceEdgeMap_isClosedEmbedding _ _).comp (standardEdgeCoordinates p.2).isClosedEmbedding

lemma standardEdgeMap_interior_image (p : ZMod m × Fin (2 * k)) :
    standardEdgeMap p '' {x : closedBall (0 : Fin 1 → ℝ) 1 | ‖x.val‖ < 1} = openEdge p := by
  ext q
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨standardEdgeCoordinates p.2 x,
      (cellIntervalCoordinates_interior _ _ _ x).mpr hx⟩,rfl⟩
  · rintro ⟨s,rfl⟩
    let x := (standardEdgeCoordinates p.2).symm s.val
    have he : standardEdgeCoordinates p.2 x = s.val := Homeomorph.apply_symm_apply _ _
    refine ⟨x, ?_, ?_⟩
    · apply (cellIntervalCoordinates_interior _ _ _ x).mp
      change (standardEdgeCoordinates p.2 x).val ∈ _
      rw [he]
      exact s.property
    · change faceEdgeMap _ _ (standardEdgeCoordinates p.2 x) = _
      rw [he]
      rfl

lemma standardEdgeMap_attaches (p : ZMod m × Fin (2 * k))
    (x : closedBall (0 : Fin 1 → ℝ) 1) (hx : ‖x.val‖ = 1) :
    (coordinate (standardEdgeMap p x)).val ∈ Surface.punctures k := by
  have he := cellIntervalCoordinates_boundary _ _ (vertexAngle_lt (k := k) (p.2.val : ℤ)) x hx
  change (Circle.exp (standardEdgeCoordinates p.2 x).val : ℂ) ∈ Surface.punctures k
  rcases he with he | he
  · change (standardEdgeCoordinates p.2 x).val = _ at he
    rw [he]
    exact vertexAngle_mem_punctures _
  · change (standardEdgeCoordinates p.2 x).val = _ at he
    rw [he]
    exact vertexAngle_mem_punctures _

def faceCellPartialEquiv (i : ZMod (2 * m)) : PartialEquiv (Fin 2 → ℝ) (FilledChain k m) :=
  closedCellPartialEquiv (standardFaceMap i) (standardFaceMap_isClosedEmbedding i)

def edgeCellPartialEquiv (p : ZMod m × Fin (2 * k)) :
    PartialEquiv (Fin 1 → ℝ) (FilledChain k m) :=
  closedCellPartialEquiv (standardEdgeMap p) (standardEdgeMap_isClosedEmbedding p)

lemma faceCellPartialEquiv_target (i : ZMod (2 * m)) :
    (faceCellPartialEquiv (k := k) i).target = openFace i := by
  change standardFaceMap i '' {x | x.val ∈ ball 0 1} = _
  simpa only [mem_ball, dist_zero_right] using standardFaceMap_interior_image i

lemma edgeCellPartialEquiv_target (p : ZMod m × Fin (2 * k)) :
    (edgeCellPartialEquiv p).target = openEdge p := by
  change standardEdgeMap p '' {x | x.val ∈ ball 0 1} = _
  simpa only [mem_ball, dist_zero_right] using standardEdgeMap_interior_image p

end KsIndex.KarcherData.DiskCompactification
