module

public import KsIndexLean.KarcherCompactEdgeMaps

@[expose] public section


/-! Zero-cell characteristic maps at the filled punctures. -/
noncomputable section
open Set Metric Topology
namespace KsIndex.KarcherData.DiskCompactification
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

abbrev VertexIndex (k : ℕ) := {w : ℂ // w ∈ punctureFinset k}

def standardVertexMap (v : VertexIndex k) (_ : closedBall (0 : Fin 0 → ℝ) 1) :
    FilledChain k m := vertex v.val ((mem_punctureFinset h.out).mp v.property)

lemma standardVertexMap_isClosedEmbedding (v : VertexIndex k) :
    IsClosedEmbedding (standardVertexMap (m := m) v) :=
  continuous_const.isClosedEmbedding (fun _ _ _ => Subsingleton.elim _ _)

def vertexCellPartialEquiv (v : VertexIndex k) :
    PartialEquiv (Fin 0 → ℝ) (FilledChain k m) :=
  closedCellPartialEquiv (standardVertexMap v) (standardVertexMap_isClosedEmbedding v)

lemma vertexCellPartialEquiv_target (v : VertexIndex k) :
    (vertexCellPartialEquiv (m := m) v).target =
      {vertex v.val ((mem_punctureFinset h.out).mp v.property)} := by
  ext q
  constructor
  · rintro ⟨x,hx,rfl⟩
    rfl
  · intro hq
    refine ⟨⟨0,by simp⟩, by simp, ?_⟩
    exact (Set.mem_singleton_iff.mp hq).symm

lemma standardVertices_cover :
    (⋃ v : VertexIndex k, range (standardVertexMap (m := m) v)) =
      {q : FilledChain k m | (coordinate q).val ∈ Surface.punctures k} := by
  ext q
  constructor
  · intro hq
    obtain ⟨v,x,rfl⟩ := Set.mem_iUnion.mp hq
    exact (mem_punctureFinset h.out).mp v.property
  · intro hq
    refine Set.mem_iUnion.mpr ⟨⟨(coordinate q).val, (mem_punctureFinset h.out).mpr hq⟩,
      ⟨0,by simp⟩, ?_⟩
    exact ((coordinate_eq_vertex_iff _ hq q).mp rfl).symm

end KsIndex.KarcherData.DiskCompactification
