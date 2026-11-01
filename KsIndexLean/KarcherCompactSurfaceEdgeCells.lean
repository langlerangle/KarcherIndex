module

public import KsIndexLean.KarcherCompactSurfaceSeamSigns

@[expose] public section


/-! Distinct open edge cells represented on the even faces. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData.DiskCompactification
open PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

omit h in
lemma evenCopyIndex_injective : Function.Injective (evenCopyIndex (m := m)) := by
  intro i j he
  have hv := congrArg ZMod.val he
  rw [evenCopyIndex_val, evenCopyIndex_val] at hv
  apply ZMod.val_injective
  omega

omit h in
lemma evenCopyIndex_ne_oddCopyIndex (i j : ZMod m) : evenCopyIndex i ≠ oddCopyIndex j := by
  intro he
  have hv := congrArg ZMod.val he
  rw [evenCopyIndex_val, oddCopyIndex_val] at hv
  omega

/-- Different even faces have no common nonvertex points. -/
lemma evenFace_eq_index {i j : ZMod m} {z v : ClosedDisk}
    (hz : z.val ∉ Surface.punctures k)
    (he : faceMap (k := k) (evenCopyIndex i) z = faceMap (evenCopyIndex j) v) : i = j := by
  have hr := Quotient.exact he
  rcases hr.2 with hp | hi | hn | hn
  · exact (hz hp).elim
  · exact evenCopyIndex_injective hi
  · rw [evenCopyIndex_succ] at hn
    exact (evenCopyIndex_ne_oddCopyIndex j i hn.1).elim
  · rw [evenCopyIndex_succ] at hn
    exact (evenCopyIndex_ne_oddCopyIndex i j hn.1).elim

abbrev OpenEdgeParameter (k : ℕ) (t : Fin (2 * k)) :=
  {s : EdgeInterval k (t.val : ℤ) //
    s.val ∈ Ioo (vertexAngle k (t.val : ℤ)) (vertexAngle k (t.val + 1 : ℤ))}

def openEdgeMap (p : ZMod m × Fin (2 * k)) (s : OpenEdgeParameter k p.2) :
    FilledChain k m := faceEdgeMap (evenCopyIndex p.1) (p.2.val : ℤ) s.val

def openEdge (p : ZMod m × Fin (2 * k)) : Set (FilledChain k m) := range (openEdgeMap p)

/-- Equality of interior edge points forces equality of the two cell labels. -/
lemma openEdgeMap_index_unique {p q : ZMod m × Fin (2 * k)}
    (s : OpenEdgeParameter k p.2) (u : OpenEdgeParameter k q.2)
    (he : openEdgeMap p s = openEdgeMap q u) : p = q := by
  have hz : (edgeParameter (p.2.val : ℤ) s.val).val ∉ Surface.punctures k :=
    edgeParameter_interior_not_puncture _ _ s.property
  have hj : p.1 = q.1 := evenFace_eq_index hz he
  have hc : edgeParameter (p.2.val : ℤ) s.val = edgeParameter (q.2.val : ℤ) u.val :=
    congrArg coordinate he
  have ht := edgeParameter_interior_index_unique p.2 q.2 s.val u.val s.property u.property hc
  exact Prod.ext hj ht

lemma openEdges_pairwiseDisjoint : Pairwise (fun p q : ZMod m × Fin (2 * k) =>
    Disjoint (openEdge p) (openEdge q)) := by
  intro p q hpq
  apply Set.disjoint_left.mpr
  rintro w ⟨s,rfl⟩ ⟨u,hu⟩
  exact hpq (openEdgeMap_index_unique s u hu.symm)

lemma openEdge_nonempty (p : ZMod m × Fin (2 * k)) : (openEdge p).Nonempty := by
  let a := vertexAngle k (p.2.val : ℤ)
  let b := vertexAngle k (p.2.val + 1 : ℤ)
  have hab : a < b := vertexAngle_lt _
  have hmid : (a + b) / 2 ∈ Ioo a b := by constructor <;> linarith
  let s : OpenEdgeParameter k p.2 := ⟨⟨(a + b) / 2, hmid.1.le, hmid.2.le⟩, hmid⟩
  exact ⟨openEdgeMap p s, s, rfl⟩

lemma openEdge_injective : Function.Injective (openEdge (k := k) (m := m)) := by
  intro p q hpq
  obtain ⟨w,hw⟩ := openEdge_nonempty p
  have hq : w ∈ openEdge q := hpq ▸ hw
  obtain ⟨s,rfl⟩ := hw
  obtain ⟨u,hu⟩ := hq
  exact openEdgeMap_index_unique s u hu.symm

/-- The actual distinct open edge images are counted, not the unglued face boundaries. -/
theorem openEdge_card : Nat.card (range (openEdge (k := k) (m := m))) = 2 * m * k := by
  rw [← Nat.card_congr (Equiv.ofInjective _ openEdge_injective)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card, Fintype.card_fin]
  ring

/-- The edge interiors cover exactly the boundary with its vertices removed. -/
theorem openEdges_cover :
    (⋃ p : ZMod m × Fin (2 * k), openEdge p) =
      {q : FilledChain k m | ‖(coordinate q).val‖ = 1 ∧
        (coordinate q).val ∉ Surface.punctures k} := by
  ext q
  constructor
  · intro hq
    obtain ⟨p,s,rfl⟩ := Set.mem_iUnion.mp hq
    exact ⟨faceEdgeMap_coordinate_norm _ _ _,
      edgeParameter_interior_not_puncture _ _ s.property⟩
  · intro hq
    obtain ⟨p,rfl⟩ := Quotient.mk_surjective q
    obtain ⟨t,s,he⟩ := exists_finite_edgeParameter (k := k) p.2 hq.1
    have hn : (Circle.exp s.val : ℂ) ∉ Surface.punctures k := by
      change (edgeParameter (t.val : ℤ) s).val ∉ Surface.punctures k
      rw [he]
      exact hq.2
    have hs : s.val ∈ Ioo (vertexAngle k (t.val : ℤ))
        (vertexAngle k (t.val + 1 : ℤ)) := by
      constructor
      · by_contra hh
        have heq : s.val = vertexAngle k (t.val : ℤ) := le_antisymm (by linarith) s.property.1
        rw [heq] at hn
        exact hn (vertexAngle_mem_punctures _)
      · by_contra hh
        have heq : s.val = vertexAngle k (t.val + 1 : ℤ) :=
          le_antisymm s.property.2 (by linarith)
        rw [heq] at hn
        exact hn (vertexAngle_mem_punctures _)
    have hpoint : faceEdgeMap (k := k) p.1 (t.val : ℤ) s = Quotient.mk _ p := by
      change faceMap p.1 (edgeParameter (t.val : ℤ) s) = faceMap p.1 p.2
      rw [he]
    obtain ⟨j, hj | hj⟩ := copyIndex_cases p.1
    · refine Set.mem_iUnion.mpr ⟨(j,t), ⟨s,hs⟩, ?_⟩
      change faceEdgeMap (evenCopyIndex j) (t.val : ℤ) s = _
      rw [← hj]
      exact hpoint
    · have ht : t.val % 2 = 0 ∨ t.val % 2 = 1 := by omega
      rcases ht with ht | ht
      · refine Set.mem_iUnion.mpr ⟨(j + 1,t), ⟨s,hs⟩, ?_⟩
        change faceEdgeMap (evenCopyIndex (j + 1)) (t.val : ℤ) s = _
        rw [← faceEdgeMap_odd_even j t.val s hs ht, ← hj]
        exact hpoint
      · refine Set.mem_iUnion.mpr ⟨(j,t), ⟨s,hs⟩, ?_⟩
        change faceEdgeMap (evenCopyIndex j) (t.val : ℤ) s = _
        rw [faceEdgeMap_even_odd j t.val s hs ht, ← hj]
        exact hpoint

end KsIndex.KarcherData.DiskCompactification
