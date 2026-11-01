module

/-
KsIndexLean — the closed staircase formula and resonance arithmetic.

Specializes `BandArithmetic` to the spectral threshold `alphaStar`, giving
the open-band floor count and the resonant endpoint count. Subtraction-free
identities control the natural-number subtractions, including at resonance.

These are arithmetic formulas for the circle model. `K3IndexComplete` and
`PaperChainNullityExact` identify the counts on the chain carrier;
`KarcherGeometricCapstone` gives the actual EW quotient formulas.
-/
public import KsIndexLean.BandArithmetic
public import KsIndexLean.Staircase

@[expose] public section


noncomputable section

namespace KsIndex.Staircase

/-- The sum-based `bandCount` is the cardinality of the abstract open band. -/
lemma bandCount_eq_card (m : ℕ) :
    bandCount m = (BandArithmetic.band alphaStar m).card := by
  classical
  simp only [bandCount, BandArithmetic.band, Set.mem_Ioo]
  rw [Finset.card_filter]

/-- Subtraction-free staircase count, valid also at resonance. -/
theorem bandCount_add (m : ℕ) (hm : 1 ≤ m) :
    bandCount m + 2 * ⌊(m : ℝ) * alphaStar⌋₊ + 1 = m := by
  rw [bandCount_eq_card]
  exact BandArithmetic.band_card_add alphaStar_pos alphaStar_lt_half hm

/-- The open middle-band count in closed form. -/
theorem bandCount_eq_floor (m : ℕ) (hm : 1 ≤ m) :
    bandCount m = m - 2 * ⌊(m : ℝ) * alphaStar⌋₊ - 1 := by
  have := bandCount_add m hm
  omega

/-- Bounds recording why both natural subtractions in the model index are exact. -/
lemma modelIndex_sub_bounds (m : ℕ) (hm : 1 ≤ m) :
    4 * ⌊(m : ℝ) * alphaStar⌋₊ ≤ 6 * m ∧
      3 ≤ 6 * m - 4 * ⌊(m : ℝ) * alphaStar⌋₊ := by
  have := BandArithmetic.two_floor_add_one_le alphaStar_pos alphaStar_lt_half hm
  omega

/-- Subtraction-free model index formula; safe to cast to integers or ENat. -/
theorem modelIndex_add (m : ℕ) (hm : 1 ≤ m) :
    modelIndex m + 4 * ⌊(m : ℝ) * alphaStar⌋₊ + 3 = 6 * m := by
  rw [modelIndex_eq m hm]
  have := bandCount_add m hm
  omega

/-- The closed index formula for the circle model, including resonance.
The geometric index formula is supplied by `KarcherGeometricCapstone`. -/
theorem modelIndex_eq_floor (m : ℕ) (hm : 1 ≤ m) :
    modelIndex m = 6 * m - 4 * ⌊(m : ℝ) * alphaStar⌋₊ - 3 := by
  have := modelIndex_add m hm
  omega

open Classical in
/-- The sampled endpoint count at the concrete spectral threshold. -/
theorem resonant_endpoints_card (m : ℕ) (hm : 1 ≤ m) :
    (BandArithmetic.endpoints alphaStar m).card =
      if ∃ z : ℤ, (m : ℝ) * alphaStar = z then 2 else 0 :=
  BandArithmetic.endpoints_card alphaStar_pos alphaStar_lt_half hm

open Classical in
/-- The numerical 3/7 dichotomy, with baseline and multiplicity inserted.
`PaperChainNullityExact` identifies this count with chain nullity; the actual
geometric nullity is supplied by `KarcherGeometricCapstone`. -/
theorem resonance_bookkeeping (m : ℕ) (hm : 1 ≤ m) :
    3 + 2 * (BandArithmetic.endpoints alphaStar m).card =
      if ∃ z : ℤ, (m : ℝ) * alphaStar = z then 7 else 3 :=
  BandArithmetic.baseline_add_two_endpoints alphaStar_pos alphaStar_lt_half hm

end KsIndex.Staircase
