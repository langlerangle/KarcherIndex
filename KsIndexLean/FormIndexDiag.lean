module

/-
Finite coordinate witnesses give lower bounds for variational index and nullity.

`coordSpace F` is the span of the coordinate vectors `Pi.single i 1` for
`i ∈ F`; it has complex dimension `F.card` and vanishes outside `F`.
`card_le_formIndex` requires this subspace to lie in the chosen domain and
requires strict negativity on its nonzero vectors. `card_le_formNullity`
requires every witness vector to pair to zero against every vector of the
chosen domain, not only against other witness vectors.

These bounds specialize the suprema defining `formIndex` and `formNullity`.
They require neither a diagonal representation nor a topological structure.
`DiagForm` combines them with the finite-coordinate upper bound from
`FormIndex` to count negative and zero entries of a diagonal symbol.
-/
public import KsIndexLean.FormIndex

@[expose] public section


noncomputable section

namespace KsIndex.FormIndex

open Classical

variable {ι : Type*} [DecidableEq ι]

/-- The coordinate subspace `span {e_i : i ∈ F}` — functions supported in the finite set `F`. -/
def coordSpace (F : Finset ι) : Submodule ℂ (ι → ℂ) :=
  Submodule.span ℂ (Set.range (fun i : F => (Pi.single (i : ι) 1 : ι → ℂ)))

/-- The generating coordinate vectors are linearly independent. -/
lemma linearIndependent_coord (F : Finset ι) :
    LinearIndependent ℂ (fun i : F => (Pi.single (i : ι) 1 : ι → ℂ)) := by
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have hval := congrFun hsum (i : ι)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    Pi.zero_apply] at hval
  rw [Finset.sum_eq_single i] at hval
  · simpa using hval
  · intro j _ hji
    rw [if_neg, mul_zero]
    exact fun h => hji (Subtype.ext h.symm)
  · intro hni; exact absurd hi hni

instance coordSpace_finiteDimensional (F : Finset ι) :
    FiniteDimensional ℂ (coordSpace F) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

/-- The coordinate subspace has dimension exactly `card F`. -/
lemma coordSpace_finrank (F : Finset ι) :
    Module.finrank ℂ (coordSpace F) = F.card := by
  rw [coordSpace, finrank_span_eq_card (linearIndependent_coord F), Fintype.card_coe]

/-- Every element of `coordSpace F` vanishes off `F`. -/
lemma coordSpace_apply_eq_zero {F : Finset ι} {u : ι → ℂ} (hu : u ∈ coordSpace F)
    {i : ι} (hi : i ∉ F) : u i = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      dsimp only
      rw [Pi.single_apply, if_neg]
      exact fun h => hi (h ▸ j.2)
  | zero => rfl
  | add x y _ _ ihx ihy => simp only [Pi.add_apply, ihx, ihy, add_zero]
  | smul c x _ ih => simp only [Pi.smul_apply, smul_eq_mul, ih, mul_zero]

/-- **Coordinate lower bound for the index.**  If `Q` is negative definite on the coordinate
subspace `coordSpace F ≤ D`, then `card F ≤ formIndex Q D`. -/
theorem card_le_formIndex {Q : (ι → ℂ) → ℝ} {D : Submodule ℂ (ι → ℂ)} {F : Finset ι}
    (hle : coordSpace F ≤ D) (hneg : ∀ u ∈ coordSpace F, u ≠ 0 → Q u < 0) :
    (F.card : ℕ∞) ≤ formIndex Q D := by
  have hneg' : NegOn Q D (coordSpace F) := ⟨hle, hneg⟩
  rw [← coordSpace_finrank F]
  unfold formIndex
  exact le_iSup₂_of_le (coordSpace F) hneg'
    (le_iSup_of_le (coordSpace_finiteDimensional F) le_rfl)

/-- **Coordinate lower bound for the nullity.**  If every vector of `coordSpace F ≤ D` lies in
the radical of `B`, then `card F ≤ formNullity B D`. -/
theorem card_le_formNullity {B : (ι → ℂ) → (ι → ℂ) → ℂ} {D : Submodule ℂ (ι → ℂ)}
    {F : Finset ι} (hle : coordSpace F ≤ D)
    (hnull : ∀ u ∈ coordSpace F, ∀ v : ι → ℂ, v ∈ D → B u v = 0) :
    (F.card : ℕ∞) ≤ formNullity B D := by
  have hnull' : NullOn B D (coordSpace F) := ⟨hle, hnull⟩
  rw [← coordSpace_finrank F]
  unfold formNullity
  exact le_iSup₂_of_le (coordSpace F) hnull'
    (le_iSup_of_le (coordSpace_finiteDimensional F) le_rfl)

end KsIndex.FormIndex
