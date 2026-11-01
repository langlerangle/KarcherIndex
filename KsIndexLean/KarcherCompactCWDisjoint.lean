module

public import KsIndexLean.KarcherCompactCWCells

@[expose] public section


/-! Disjointness of all open cells, including cells of different dimensions. -/
noncomputable section
open Set Metric Topology
namespace KsIndex.KarcherData.DiskCompactification
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

lemma mem_openFace_norm_lt {i : ZMod (2 * m)} {q : FilledChain k m} (hq : q ∈ openFace i) :
    ‖(coordinate q).val‖ < 1 := by
  obtain ⟨z,hz,rfl⟩ := hq
  exact hz

lemma mem_openEdge_boundary {p : ZMod m × Fin (2 * k)} {q : FilledChain k m}
    (hq : q ∈ openEdge p) : ‖(coordinate q).val‖ = 1 ∧
      (coordinate q).val ∉ Surface.punctures k := by
  have hu : q ∈ ⋃ p, openEdge p := Set.mem_iUnion.mpr ⟨p,hq⟩
  rw [openEdges_cover] at hu
  exact hu

lemma compactCell_target_unique {n l : ℕ} (i : compactCell k m n) (j : compactCell k m l)
    (q : FilledChain k m) (hi : q ∈ (compactCellMap n i).target)
    (hj : q ∈ (compactCellMap l j).target) : Sigma.mk n i = Sigma.mk l j := by
  rcases n with _ | _ | _ | n <;> rcases l with _ | _ | _ | l
  all_goals try exact PEmpty.elim i
  all_goals try exact PEmpty.elim j
  · rw [compactCellMap_target_zero, Set.mem_singleton_iff] at hi hj
    have he : i.val = j.val := by
      simpa only [coordinate_vertex] using congrArg (fun q : FilledChain k m =>
        (coordinate q).val) (hi.symm.trans hj)
    have hij : i = j := Subtype.ext he
    subst j
    rfl
  · rw [compactCellMap_target_zero, Set.mem_singleton_iff] at hi
    rw [compactCellMap_target_one] at hj
    have hn := (mem_openEdge_boundary hj).2
    rw [hi, coordinate_vertex] at hn
    exact (hn ((mem_punctureFinset h.out).mp i.property)).elim
  · rw [compactCellMap_target_zero, Set.mem_singleton_iff] at hi
    rw [compactCellMap_target_two] at hj
    have hn := mem_openFace_norm_lt hj
    rw [hi, coordinate_vertex, puncture_norm h.out ((mem_punctureFinset h.out).mp i.property)] at hn
    exact (lt_irrefl _ hn).elim
  · rw [compactCellMap_target_one] at hi
    rw [compactCellMap_target_zero, Set.mem_singleton_iff] at hj
    have hn := (mem_openEdge_boundary hi).2
    rw [hj, coordinate_vertex] at hn
    exact (hn ((mem_punctureFinset h.out).mp j.property)).elim
  · rw [compactCellMap_target_one] at hi hj
    obtain ⟨s,rfl⟩ := hi
    obtain ⟨u,hu⟩ := hj
    have hij := openEdgeMap_index_unique s u hu.symm
    subst j
    rfl
  · rw [compactCellMap_target_one] at hi
    rw [compactCellMap_target_two] at hj
    have he := (mem_openEdge_boundary hi).1
    have hl := mem_openFace_norm_lt hj
    rw [he] at hl
    exact (lt_irrefl _ hl).elim
  · rw [compactCellMap_target_two] at hi
    rw [compactCellMap_target_zero, Set.mem_singleton_iff] at hj
    have hn := mem_openFace_norm_lt hi
    rw [hj, coordinate_vertex, puncture_norm h.out ((mem_punctureFinset h.out).mp j.property)] at hn
    exact (lt_irrefl _ hn).elim
  · rw [compactCellMap_target_two] at hi
    rw [compactCellMap_target_one] at hj
    have he := (mem_openEdge_boundary hj).1
    have hl := mem_openFace_norm_lt hi
    rw [he] at hl
    exact (lt_irrefl _ hl).elim
  · rw [compactCellMap_target_two] at hi hj
    have hij : i = j := by
      by_contra hne
      exact Set.disjoint_left.mp (openFaces_pairwiseDisjoint hne) hi hj
    subst j
    rfl

lemma compactCellMap_pairwiseDisjoint :
    (univ : Set (Σ n, compactCell k m n)).PairwiseDisjoint
      (fun p => compactCellMap p.1 p.2 '' ball 0 1) := by
  intro p hp q hq hpq
  apply Set.disjoint_left.mpr
  intro x hx hy
  change x ∈ compactCellMap p.1 p.2 '' ball 0 1 at hx
  change x ∈ compactCellMap q.1 q.2 '' ball 0 1 at hy
  rw [compactCellMap_open_image (k := k) (m := m) p.1 p.2] at hx
  rw [compactCellMap_open_image (k := k) (m := m) q.1 q.2] at hy
  exact hpq (compactCell_target_unique p.2 q.2 x hx hy)

end KsIndex.KarcherData.DiskCompactification
