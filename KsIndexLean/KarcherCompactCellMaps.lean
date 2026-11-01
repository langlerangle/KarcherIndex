module

public import KsIndexLean.KarcherCompactSurfaceEdgeCells
public import KsIndexLean.CellDiskCoordinates

@[expose] public section


/-! Standard closed two-cell characteristic maps for the compact surface. -/
noncomputable section
open Set Metric Topology
namespace KsIndex.KarcherData.DiskCompactification
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

/-- The subtype convention for the complex closed ball agrees with the closed disk. -/
def closedDiskBallHomeomorph : closedBall (0 : ℂ) 1 ≃ₜ ClosedDisk :=
  Homeomorph.setCongr (by
    ext z
    change dist z 0 ≤ 1 ↔ ‖z‖ ≤ 1
    rw [dist_zero_right])

/-- Coordinates from the standard closed two-cell to the face parameter disk. -/
def standardFaceCoordinates : closedBall (0 : Fin 2 → ℝ) 1 ≃ₜ ClosedDisk :=
  cellClosedDiskHomeomorph.trans closedDiskBallHomeomorph

lemma standardFaceCoordinates_val (x : closedBall (0 : Fin 2 → ℝ) 1) :
    (standardFaceCoordinates x).val = cellDiskCoordinates x.val := rfl

lemma standardFaceCoordinates_interior (x : closedBall (0 : Fin 2 → ℝ) 1) :
    ‖(standardFaceCoordinates x).val‖ < 1 ↔ ‖x.val‖ < 1 := by
  have he : cellDiskCoordinates x.val ∈ cellDiskCoordinates '' ball 0 1 ↔ x.val ∈ ball 0 1 := by
    constructor
    · rintro ⟨y,hy,he⟩
      exact cellDiskCoordinates.injective he ▸ hy
    · intro hx
      exact ⟨x.val,hx,rfl⟩
  rw [cellDiskCoordinates_ball] at he
  simpa only [standardFaceCoordinates_val, mem_ball, dist_zero_right] using he

lemma standardFaceCoordinates_boundary (x : closedBall (0 : Fin 2 → ℝ) 1)
    (hx : ‖x.val‖ = 1) : ‖(standardFaceCoordinates x).val‖ = 1 := by
  have he : cellDiskCoordinates x.val ∈ cellDiskCoordinates '' sphere 0 1 :=
    ⟨x.val, by simpa only [mem_sphere, dist_zero_right] using hx, rfl⟩
  rw [cellDiskCoordinates_sphere] at he
  simpa only [standardFaceCoordinates_val, mem_sphere, dist_zero_right] using he

/-- The actual characteristic map of a closed two-cell. -/
def standardFaceMap (i : ZMod (2 * m)) : closedBall (0 : Fin 2 → ℝ) 1 → FilledChain k m :=
  faceMap i ∘ standardFaceCoordinates

lemma standardFaceMap_isClosedEmbedding (i : ZMod (2 * m)) :
    IsClosedEmbedding (standardFaceMap (k := k) i) :=
  (faceMap_isClosedEmbedding i).comp standardFaceCoordinates.isClosedEmbedding

lemma standardFaceMap_range (i : ZMod (2 * m)) :
    range (standardFaceMap (k := k) i) = range (faceMap (k := k) i) := by
  ext q
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨standardFaceCoordinates x,rfl⟩
  · rintro ⟨z,rfl⟩
    refine ⟨standardFaceCoordinates.symm z, ?_⟩
    simp only [standardFaceMap, Function.comp_apply, Homeomorph.apply_symm_apply]

/-- The attaching boundary maps into the one-dimensional boundary locus. -/
lemma standardFaceMap_boundary (i : ZMod (2 * m))
    (x : closedBall (0 : Fin 2 → ℝ) 1) (hx : ‖x.val‖ = 1) :
    ‖(coordinate (standardFaceMap (k := k) i x)).val‖ = 1 :=
  standardFaceCoordinates_boundary x hx

/-- The characteristic maps cover the compactified surface. -/
lemma standardFaces_cover :
    (⋃ i : ZMod (2 * m), range (standardFaceMap (k := k) i)) = univ := by
  simp only [standardFaceMap_range]
  exact closedFaces_cover

/-- The standard open two-cell maps onto the previously identified open face. -/
lemma standardFaceMap_interior_image (i : ZMod (2 * m)) :
    standardFaceMap (k := k) i '' {x : closedBall (0 : Fin 2 → ℝ) 1 | ‖x.val‖ < 1} =
      openFace i := by
  ext q
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨standardFaceCoordinates x, (standardFaceCoordinates_interior x).mpr hx, rfl⟩
  · rintro ⟨z,hz,rfl⟩
    refine ⟨standardFaceCoordinates.symm z, ?_, ?_⟩
    · apply (standardFaceCoordinates_interior _).mp
      simpa only [Homeomorph.apply_symm_apply, Set.mem_ofPred_eq] using hz
    · simp only [standardFaceMap, Function.comp_apply, Homeomorph.apply_symm_apply]

/-- The attaching sphere lands in vertices or open edges, rather than in a face interior. -/
lemma standardFaceMap_attaches (i : ZMod (2 * m))
    (x : closedBall (0 : Fin 2 → ℝ) 1) (hx : ‖x.val‖ = 1) :
    (coordinate (standardFaceMap (k := k) i x)).val ∈ Surface.punctures k ∨
      standardFaceMap (k := k) i x ∈ ⋃ p : ZMod m × Fin (2 * k), openEdge p := by
  by_cases hv : (coordinate (standardFaceMap (k := k) i x)).val ∈ Surface.punctures k
  · exact Or.inl hv
  · right
    rw [openEdges_cover]
    exact ⟨standardFaceMap_boundary i x hx, hv⟩

end KsIndex.KarcherData.DiskCompactification
