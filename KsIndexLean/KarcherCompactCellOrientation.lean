module

public import KsIndexLean.KarcherCompactCellCounts

@[expose] public section


/-! Alternating signs on the actual faces and cancellation along the seam pairings.
These are cellular orientation data; no general surface-classification theorem is assumed.
-/
noncomputable section
open Set
namespace KsIndex.KarcherData.DiskCompactification
open PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

/-- The two types of half-period faces carry opposite boundary orientations. -/
def faceOrientationSign (i : ZMod (2 * m)) : ℤ :=
  if Surface.parity m i = 0 then 1 else -1

omit h in
lemma parity_evenCopyIndex (j : ZMod m) : Surface.parity m (evenCopyIndex j) = 0 := by
  simp only [evenCopyIndex, Nat.cast_mul, map_mul]
  norm_num
  rw [map_ofNat]
  exact Or.inl (by decide)

omit h in
lemma parity_oddCopyIndex (j : ZMod m) : Surface.parity m (oddCopyIndex j) = 1 := by
  rw [← evenCopyIndex_succ, map_add, map_one, parity_evenCopyIndex, zero_add]

omit h in
lemma faceOrientationSign_even (j : ZMod m) : faceOrientationSign (evenCopyIndex j) = 1 := by
  simp [faceOrientationSign, parity_evenCopyIndex]

omit h in
lemma faceOrientationSign_odd (j : ZMod m) : faceOrientationSign (oddCopyIndex j) = -1 := by
  simp [faceOrientationSign, parity_oddCopyIndex]

omit h in
lemma faceOrientationSign_succ (i : ZMod (2 * m)) :
    faceOrientationSign (i + 1) = -faceOrientationSign i := by
  obtain ⟨j,rfl | rfl⟩ := copyIndex_cases i
  · rw [evenCopyIndex_succ, faceOrientationSign_odd, faceOrientationSign_even]
  · rw [oddCopyIndex_succ, faceOrientationSign_even, faceOrientationSign_odd]
    norm_num

/-- The other incident face for an edge represented on an even face. -/
def otherEdgeFace (p : ZMod m × Fin (2 * k)) : ZMod (2 * m) :=
  if p.2.val % 2 = 1 then oddCopyIndex p.1 else oddCopyIndex (p.1 - 1)

omit h in
lemma otherEdgeFace_ne (p : ZMod m × Fin (2 * k)) :
    otherEdgeFace p ≠ evenCopyIndex p.1 := by
  unfold otherEdgeFace
  split <;> exact (evenCopyIndex_ne_oddCopyIndex _ _).symm

omit h in
/-- Each chosen edge pairing has cancelling boundary signs. -/
lemma edge_face_signs_cancel (p : ZMod m × Fin (2 * k)) :
    faceOrientationSign (evenCopyIndex p.1) + faceOrientationSign (otherEdgeFace p) = 0 := by
  unfold otherEdgeFace
  split <;> rw [faceOrientationSign_even, faceOrientationSign_odd] <;> norm_num

/-- The two incident faces use exactly the same increasing angular edge parameter. -/
lemma otherEdgeFace_same_parameter (p : ZMod m × Fin (2 * k))
    (s : OpenEdgeParameter k p.2) :
    faceEdgeMap (k := k) (otherEdgeFace p) (p.2.val : ℤ) s.val = openEdgeMap p s := by
  unfold otherEdgeFace
  split
  · exact (faceEdgeMap_even_odd p.1 p.2.val s.val s.property (by assumption)).symm
  · have ht : p.2.val % 2 = 0 := by omega
    have he := faceEdgeMap_odd_even (p.1 - 1) p.2.val s.val s.property ht
    simpa only [sub_add_cancel, openEdgeMap] using he

/-- Every nonvertex edge has two distinct incident faces with opposite boundary signs,
verified using the actual quotient maps. -/
theorem edge_pair_orientation_data (p : ZMod m × Fin (2 * k)) :
    otherEdgeFace p ≠ evenCopyIndex p.1 ∧
    faceOrientationSign (evenCopyIndex p.1) + faceOrientationSign (otherEdgeFace p) = 0 ∧
    ∀ s : OpenEdgeParameter k p.2,
      faceEdgeMap (k := k) (otherEdgeFace p) (p.2.val : ℤ) s.val = openEdgeMap p s :=
  ⟨otherEdgeFace_ne p, edge_face_signs_cancel p, otherEdgeFace_same_parameter p⟩

/-- No third face can meet the interior of an edge. -/
lemma edge_incident_faces_only (p : ZMod m × Fin (2 * k))
    (s : OpenEdgeParameter k p.2) (i : ZMod (2 * m))
    (he : faceEdgeMap (k := k) i (p.2.val : ℤ) s.val = openEdgeMap p s) :
    i = evenCopyIndex p.1 ∨ i = otherEdgeFace p := by
  have hn := edgeParameter_interior_not_puncture (p.2.val : ℤ) s.val s.property
  obtain ⟨j,rfl | rfl⟩ := copyIndex_cases i
  · left
    exact congrArg evenCopyIndex (evenFace_eq_index hn he)
  · right
    by_cases ht : p.2.val % 2 = 1
    · have hp := faceEdgeMap_even_odd j p.2.val s.val s.property ht
      have hj : j = p.1 := evenFace_eq_index hn (hp.trans he)
      simp only [otherEdgeFace, ht, ite_true, hj]
    · have ht0 : p.2.val % 2 = 0 := by omega
      have hp := faceEdgeMap_odd_even j p.2.val s.val s.property ht0
      have hj : j + 1 = p.1 := evenFace_eq_index hn (hp.symm.trans he)
      have hj' : j = p.1 - 1 := by rw [← hj]; simp
      simp only [otherEdgeFace, ht, ite_false, hj']

/-- Opposite face signs hold along every actual nonvertex face identification. -/
lemma face_signs_cancel_of_identification {i j : ZMod (2 * m)} (hij : i ≠ j)
    {z v : ClosedDisk} (hz : z.val ∉ Surface.punctures k)
    (he : faceMap (k := k) i z = faceMap j v) :
    faceOrientationSign i + faceOrientationSign j = 0 := by
  obtain ⟨_, hp | hp | hp⟩ := (faceMap_eq_iff_boundary hij z v).mp he
  · exact (hz hp).elim
  · rw [hp.1, faceOrientationSign_succ]
    ring
  · rw [hp.1, faceOrientationSign_succ]
    ring

end KsIndex.KarcherData.DiskCompactification
