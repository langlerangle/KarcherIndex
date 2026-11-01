module

public import KsIndexLean.KarcherCompactCWComplex

@[expose] public section


/-! Cell counts of the finite CW structure and their alternating sum. -/
noncomputable section
open Set
namespace KsIndex.KarcherData.DiskCompactification
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

omit [NeZero m] in
lemma compactCell_card_zero : Nat.card (compactCell k m 0) = 2 * k := by
  change Nat.card (VertexIndex k) = _
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  exact punctureFinset_card h.out

omit h in
lemma compactCell_card_one : Nat.card (compactCell k m 1) = 2 * m * k := by
  change Nat.card (ZMod m × Fin (2 * k)) = _
  rw [Nat.card_prod, Nat.card_eq_fintype_card, ZMod.card, Nat.card_fin]
  ring

omit h in
lemma compactCell_card_two : Nat.card (compactCell k m 2) = 2 * m := by
  let : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  change Nat.card (ZMod (2 * m)) = _
  rw [Nat.card_eq_fintype_card, ZMod.card]

/-- The computed counts are counts of Mathlib's CW cells on the compact surface. -/
theorem compactSurfaceCW_cell_counts :
    letI := compactSurfaceCWComplex (k := k) (m := m)
    Nat.card (Topology.CWComplex.cell (univ : Set (FilledChain k m)) 0) = 2 * k ∧
    Nat.card (Topology.CWComplex.cell (univ : Set (FilledChain k m)) 1) = 2 * m * k ∧
    Nat.card (Topology.CWComplex.cell (univ : Set (FilledChain k m)) 2) = 2 * m :=
  ⟨compactCell_card_zero, compactCell_card_one, compactCell_card_two⟩

/-- The alternating cell count, without a separate assertion of orientability or genus. -/
theorem compactSurfaceCW_alternating_count :
    (Nat.card (compactCell k m 0) : ℤ) - Nat.card (compactCell k m 1) +
      Nat.card (compactCell k m 2) = 2 - 2 * ((k : ℤ) - 1) * ((m : ℤ) - 1) := by
  rw [compactCell_card_zero, compactCell_card_one, compactCell_card_two]
  push_cast
  ring

end KsIndex.KarcherData.DiskCompactification
