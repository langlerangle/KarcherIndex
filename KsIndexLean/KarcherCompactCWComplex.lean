module

public import KsIndexLean.KarcherCompactCWDisjoint

@[expose] public section


/-! A finite CW structure on the actual compactified EW quotient. -/
noncomputable section
open Set Metric Topology
namespace KsIndex.KarcherData.DiskCompactification
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

lemma compactCell_target_subset_closed_image (n : ℕ) (i : compactCell k m n) :
    (compactCellMap n i).target ⊆ compactCellMap n i '' closedBall 0 1 := by
  rw [← compactCellMap_open_image (k := k) (m := m) n i]
  exact Set.image_mono ball_subset_closedBall

lemma vertex_mem_closed_cell {q : FilledChain k m}
    (hq : (coordinate q).val ∈ Surface.punctures k) :
    ∃ v : compactCell k m 0, q ∈ compactCellMap 0 v '' closedBall 0 1 := by
  have hu : q ∈ ⋃ v : VertexIndex k, range (standardVertexMap (m := m) v) := by
    rw [standardVertices_cover]
    exact hq
  obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hu
  refine ⟨v, ?_⟩
  rw [compactCellMap_closed_image (k := k) (m := m) 0 v]
  exact hv

lemma compactCellMap_attaches (n : ℕ) (i : compactCell k m n) :
    MapsTo (compactCellMap n i) (sphere 0 1)
      (⋃ (l < n) (j : compactCell k m l), compactCellMap l j '' closedBall 0 1) := by
  intro x hx
  have hxc : x ∈ closedBall 0 1 := sphere_subset_closedBall hx
  have he : compactCellMap n i x = compactClosedMap n i ⟨x,hxc⟩ :=
    closedCellExtension_apply _ ⟨x,hxc⟩
  rw [he]
  have hn : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
  rcases n with _ | _ | _ | n
  · have hx0 : x = 0 := Subsingleton.elim _ _
    simp only [hx0, norm_zero, zero_ne_one] at hn
  · have hv := standardEdgeMap_attaches i ⟨x,hxc⟩ hn
    obtain ⟨v,hv⟩ := vertex_mem_closed_cell hv
    exact Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨by omega,
      Set.mem_iUnion.mpr ⟨v,hv⟩⟩⟩
  · have hb := standardFaceMap_attaches (k := k) i ⟨x,hxc⟩ hn
    rcases hb with hv | he
    · obtain ⟨v,hv⟩ := vertex_mem_closed_cell hv
      exact Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨by omega,
        Set.mem_iUnion.mpr ⟨v,hv⟩⟩⟩
    · obtain ⟨p,hp⟩ := Set.mem_iUnion.mp he
      have ht : standardFaceMap i ⟨x,hxc⟩ ∈ (compactCellMap (k := k) (m := m) 1 p).target := by
        rw [compactCellMap_target_one (k := k) (m := m) p]
        exact hp
      exact Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨by omega,
        Set.mem_iUnion.mpr ⟨p, compactCell_target_subset_closed_image 1 p ht⟩⟩⟩
  · exact PEmpty.elim i

/-- The disk-chain cells form a genuine finite CW decomposition of the compactification. -/
@[instance_reducible]
def compactSurfaceCWComplex : Topology.CWComplex (univ : Set (FilledChain k m)) :=
  Topology.CWComplex.mkFinite univ (compactCell k m) compactCellMap
    compactCell_eventually_empty (fun _ => inferInstance) compactCellMap_source
    compactCellMap_continuousOn compactCellMap_continuousOn_symm
    compactCellMap_pairwiseDisjoint compactCellMap_attaches compactCellMap_cover

theorem compactSurfaceCWComplex_finite :
    letI := compactSurfaceCWComplex (k := k) (m := m)
    Topology.CWComplex.Finite (univ : Set (FilledChain k m)) := by
  exact Topology.CWComplex.finite_mkFinite univ (compactCell k m) compactCellMap
    compactCell_eventually_empty (fun _ => inferInstance) compactCellMap_source
    compactCellMap_continuousOn compactCellMap_continuousOn_symm
    compactCellMap_pairwiseDisjoint compactCellMap_attaches compactCellMap_cover

end KsIndex.KarcherData.DiskCompactification
