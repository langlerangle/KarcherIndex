module

public import KsIndexLean.KarcherCompactVertexMaps

@[expose] public section


/-! The dimension-indexed finite cells of the compactified EW quotient. -/
noncomputable section
open Set Metric Topology
namespace KsIndex.KarcherData.DiskCompactification
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

def compactCell (k m : ℕ) : ℕ → Type
  | 0 => VertexIndex k
  | 1 => ZMod m × Fin (2 * k)
  | 2 => ZMod (2 * m)
  | _ + 3 => PEmpty

def compactClosedMap : (n : ℕ) → compactCell k m n →
    closedBall (0 : Fin n → ℝ) 1 → FilledChain k m
  | 0, v => standardVertexMap v
  | 1, p => standardEdgeMap p
  | 2, i => standardFaceMap i
  | _ + 3, e => PEmpty.elim e

lemma compactClosedMap_isClosedEmbedding (n : ℕ) (i : compactCell k m n) :
    IsClosedEmbedding (compactClosedMap n i) := by
  rcases n with _ | _ | _ | n
  · exact standardVertexMap_isClosedEmbedding i
  · exact standardEdgeMap_isClosedEmbedding i
  · exact standardFaceMap_isClosedEmbedding i
  · exact PEmpty.elim i

def compactCellMap (n : ℕ) (i : compactCell k m n) :
    PartialEquiv (Fin n → ℝ) (FilledChain k m) :=
  closedCellPartialEquiv (compactClosedMap n i) (compactClosedMap_isClosedEmbedding n i)

lemma compactCellMap_source (n : ℕ) (i : compactCell k m n) :
    (compactCellMap n i).source = ball 0 1 := rfl

lemma compactCellMap_continuousOn (n : ℕ) (i : compactCell k m n) :
    ContinuousOn (compactCellMap n i) (closedBall 0 1) :=
  closedCellExtension_continuousOn _ (compactClosedMap_isClosedEmbedding n i).continuous

lemma compactCellMap_continuousOn_symm (n : ℕ) (i : compactCell k m n) :
    ContinuousOn (compactCellMap n i).symm (compactCellMap n i).target :=
  closedCellPartialEquiv_continuousOn_symm _ _

lemma compactCellMap_closed_image (n : ℕ) (i : compactCell k m n) :
    compactCellMap n i '' closedBall 0 1 = range (compactClosedMap n i) :=
  closedCellPartialEquiv_closed_image _ _

lemma compactCellMap_open_image (n : ℕ) (i : compactCell k m n) :
    compactCellMap n i '' ball 0 1 = (compactCellMap n i).target :=
  (compactCellMap n i).image_source_eq_target

lemma compactCellMap_target_zero (v : compactCell k m 0) :
    (compactCellMap 0 v).target =
      {vertex v.val ((mem_punctureFinset h.out).mp v.property)} :=
  vertexCellPartialEquiv_target v

lemma compactCellMap_target_one (p : compactCell k m 1) :
    (compactCellMap 1 p).target = openEdge p := edgeCellPartialEquiv_target p

lemma compactCellMap_target_two (i : compactCell k m 2) :
    (compactCellMap 2 i).target = openFace i := faceCellPartialEquiv_target i

instance compactCell_finite (n : ℕ) : Finite (compactCell k m n) := by
  rcases n with _ | _ | _ | n
  · exact inferInstanceAs (Finite (VertexIndex k))
  · exact inferInstanceAs (Finite (ZMod m × Fin (2 * k)))
  · let : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
    exact inferInstanceAs (Finite (ZMod (2 * m)))
  · exact inferInstanceAs (Finite PEmpty)

omit h [NeZero m] in
lemma compactCell_eventually_empty : ∀ᶠ n in Filter.atTop, IsEmpty (compactCell k m n) := by
  filter_upwards [Filter.eventually_ge_atTop 3] with n hn
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm]
  change IsEmpty PEmpty
  infer_instance

lemma compactCellMap_cover :
    (⋃ (n : ℕ) (i : compactCell k m n), compactCellMap n i '' closedBall 0 1) = univ := by
  apply Set.eq_univ_of_forall
  intro q
  have hq : q ∈ ⋃ i : ZMod (2 * m), range (standardFaceMap (k := k) i) := by
    rw [standardFaces_cover]
    trivial
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hq
  exact Set.mem_iUnion.mpr ⟨2, Set.mem_iUnion.mpr ⟨i, by
    rw [compactCellMap_closed_image (k := k) (m := m) 2 i]
    exact hi⟩⟩

end KsIndex.KarcherData.DiskCompactification
