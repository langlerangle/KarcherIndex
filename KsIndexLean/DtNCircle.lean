module

/-
KsIndexLean — DtNCircle: the half-period Dirichlet-to-Neumann operator `nop_k` at the circle
level, and its index/nullity ([ksindexi] `DtN-momentum`, `D_and_N_half_period` Neumann row).

The Fourier multiplier `nop_k` of `DtN-momentum` acts on the mean-zero space `Ḣ^{1/2}(S¹)`
(coefficients indexed by the NONZERO integers) with symbol

    `σ_k(ℓ) = (ℓ² − (k−1)²) / |ℓ|`,      `ℓ ≠ 0`.

By the diagonal-form signature theorem (`DiagForm`), its Morse index and nullity are the
sign-counts of the symbol:

    `ind(nop_k) = #{ℓ ≠ 0 : |ℓ| < k−1} = 2k − 4`,
    `nul(nop_k) = #{ℓ ≠ 0 : |ℓ| = k−1} = 2`,

which is the `⊕_{j≠0}` Neumann content of `D_and_N_half_period` (`ind_N(Ξ_k^{(0,π)}) = 2k−3`
is this `2k−4` plus the `+1` `ℓ = 0` tanh zero-mode, handled separately in the paper).

Mean-zero is encoded by the nonzero integer index type `NZ`, so the zero
Fourier mode is excluded from the symbol. The carrier used here is the
absolute-energy domain `DomDiag (dtnSymbol k)`, defined by summability of
`|σ_k(ℓ)| * ‖u ℓ‖²`. Its identification with a geometric trace space and the
addition of the zero-mode contribution belong to the separate transports.
The two count theorems below assume `k ≥ 3`.
-/
public import KsIndexLean.DiagForm

@[expose] public section


noncomputable section

namespace KsIndex.DtNCircle

open Classical KsIndex.FormIndex KsIndex.DiagForm

/-- The nonzero integers — the mode index set of `Ḣ^{1/2}(S¹)`. -/
abbrev NZ := {ℓ : ℤ // ℓ ≠ 0}

/-- The DtN symbol `σ_k(ℓ) = (ℓ² − (k−1)²)/|ℓ|`. -/
def dtnSymbol (k : ℕ) (ℓ : NZ) : ℝ :=
  ((ℓ.val : ℝ) ^ 2 - ((k : ℝ) - 1) ^ 2) / |(ℓ.val : ℝ)|

lemma absval_pos (ℓ : NZ) : (0 : ℝ) < |(ℓ.val : ℝ)| :=
  abs_pos.mpr (by exact_mod_cast ℓ.2)

/-! ### Integer square/abs helpers -/

lemma abs_lt_iff_sq (a b : ℤ) (hb : 0 ≤ b) : |a| < b ↔ a ^ 2 < b ^ 2 := by
  constructor <;> intro h <;> nlinarith [abs_nonneg a, sq_abs a, abs_le.mp (le_refl |a|)]

lemma abs_le_iff_sq (a b : ℤ) (hb : 0 ≤ b) : |a| ≤ b ↔ a ^ 2 ≤ b ^ 2 := by
  constructor <;> intro h <;> nlinarith [abs_nonneg a, sq_abs a]

lemma abs_eq_iff_sq (a b : ℤ) (hb : 0 ≤ b) : |a| = b ↔ a ^ 2 = b ^ 2 := by
  constructor
  · intro h; rw [← sq_abs, h]
  · intro h
    have := abs_nonneg a
    nlinarith [sq_abs a]

/-! ### Sign of the symbol -/

lemma dtn_num_cast (k : ℕ) (ℓ : NZ) :
    ((ℓ.val : ℝ) ^ 2 - ((k : ℝ) - 1) ^ 2 < 0 ↔ ℓ.val ^ 2 < ((k : ℤ) - 1) ^ 2) := by
  rw [sub_neg]
  constructor
  · intro h; exact_mod_cast (by push_cast at h ⊢; linarith : (ℓ.val : ℝ) ^ 2 < ((k:ℝ) - 1) ^ 2)
  · intro h
    have : ((ℓ.val ^ 2 : ℤ) : ℝ) < (((k : ℤ) - 1) ^ 2 : ℤ) := by exact_mod_cast h
    push_cast at this ⊢; linarith

lemma dtn_lt_zero_iff (hk : 2 ≤ k) (ℓ : NZ) :
    dtnSymbol k ℓ < 0 ↔ |ℓ.val| ≤ (k : ℤ) - 2 := by
  have hB := absval_pos ℓ
  rw [dtnSymbol, div_lt_iff₀ hB, zero_mul, dtn_num_cast k ℓ,
    ← abs_lt_iff_sq _ _ (by omega : (0:ℤ) ≤ (k:ℤ) - 1)]
  omega

lemma dtn_eq_zero_iff (hk : 2 ≤ k) (ℓ : NZ) :
    dtnSymbol k ℓ = 0 ↔ |ℓ.val| = (k : ℤ) - 1 := by
  have hB := absval_pos ℓ
  rw [dtnSymbol, div_eq_zero_iff, or_iff_left hB.ne', sub_eq_zero,
    abs_eq_iff_sq _ _ (by omega : (0:ℤ) ≤ (k:ℤ) - 1)]
  constructor
  · intro h
    have : ((ℓ.val ^ 2 : ℤ) : ℝ) = (((k:ℤ) - 1) ^ 2 : ℤ) := by push_cast; push_cast at h; linarith
    exact_mod_cast this
  · intro h
    have : ((ℓ.val ^ 2 : ℤ) : ℝ) = (((k:ℤ) - 1) ^ 2 : ℤ) := by exact_mod_cast h
    push_cast at this ⊢; linarith

lemma dtn_le_zero_iff (hk : 2 ≤ k) (ℓ : NZ) :
    dtnSymbol k ℓ ≤ 0 ↔ |ℓ.val| ≤ (k : ℤ) - 1 := by
  have hB := absval_pos ℓ
  rw [dtnSymbol, div_nonpos_iff]
  rw [abs_le_iff_sq _ _ (by omega : (0:ℤ) ≤ (k:ℤ) - 1)]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact absurd h (not_le.mpr hB)
    · have : ((ℓ.val ^ 2 : ℤ) : ℝ) ≤ (((k:ℤ) - 1) ^ 2 : ℤ) := by push_cast; push_cast at h; linarith
      exact_mod_cast this
  · intro h
    refine Or.inr ⟨?_, hB.le⟩
    have : ((ℓ.val ^ 2 : ℤ) : ℝ) ≤ (((k:ℤ) - 1) ^ 2 : ℤ) := by exact_mod_cast h
    push_cast at this ⊢; linarith

/-! ### Counting the sign sets -/

/-- The nonzero integers with `|ℓ| ≤ b`, as an explicit finset. -/
def absLe (b : ℤ) : Finset NZ := (Finset.Icc (-b) b).subtype (· ≠ 0)

lemma mem_absLe {b : ℤ} {ℓ : NZ} : ℓ ∈ absLe b ↔ |ℓ.val| ≤ b := by
  rw [absLe, Finset.mem_subtype, Finset.mem_Icc, abs_le]

lemma card_absLe {b : ℤ} (hb : 0 ≤ b) : (absLe b).card = 2 * b.toNat := by
  rw [absLe, Finset.card_subtype, Finset.filter_ne',
    Finset.card_erase_of_mem (by rw [Finset.mem_Icc]; omega), Int.card_Icc]
  omega

/-- Finiteness of the head set. -/
lemma dtn_head_finite (hk : 3 ≤ k) : {ℓ : NZ | dtnSymbol k ℓ ≤ 0}.Finite := by
  apply Set.Finite.subset (absLe ((k : ℤ) - 1)).finite_toSet
  intro ℓ hℓ
  rw [Finset.mem_coe, mem_absLe]
  exact (dtn_le_zero_iff (by omega) ℓ).mp hℓ

/-! ### Index and nullity of `nop_k` -/

/-- **Index of `nop_k`**: `ind = 2k − 4` on `Ḣ^{1/2}(S¹)`. -/
theorem nop_index (hk : 3 ≤ k) :
    formIndex (Qdiag (dtnSymbol k)) (DomDiag (dtnSymbol k)) = ((2 * k - 4 : ℕ) : ℕ∞) := by
  have hfin := dtn_head_finite hk
  rw [formIndex_Qdiag hfin]
  have heq : (negFinite hfin).toFinset = absLe ((k : ℤ) - 2) := by
    ext ℓ
    rw [Set.Finite.mem_toFinset, mem_absLe, Set.mem_setOf_eq]
    exact dtn_lt_zero_iff (by omega) ℓ
  rw [heq, card_absLe (by omega)]
  congr 1
  omega

/-- **Nullity of `nop_k`**: `nul = 2` on `Ḣ^{1/2}(S¹)`. -/
theorem nop_nullity (hk : 3 ≤ k) :
    formNullity (Bdiag (dtnSymbol k)) (DomDiag (dtnSymbol k)) = ((2 : ℕ) : ℕ∞) := by
  have hfin := dtn_head_finite hk
  rw [formNullity_Bdiag hfin]
  have hhead : (headFinset hfin).card = 2 * ((k : ℤ) - 1).toNat := by
    have : headFinset hfin = absLe ((k : ℤ) - 1) := by
      ext ℓ
      rw [mem_headFinset, mem_absLe]
      exact dtn_le_zero_iff (by omega) ℓ
    rw [this, card_absLe (by omega)]
  have hneg : (negFinite hfin).toFinset.card = 2 * ((k : ℤ) - 2).toNat := by
    have : (negFinite hfin).toFinset = absLe ((k : ℤ) - 2) := by
      ext ℓ
      rw [Set.Finite.mem_toFinset, mem_absLe, Set.mem_setOf_eq]
      exact dtn_lt_zero_iff (by omega) ℓ
    rw [this, card_absLe (by omega)]
  have hsplit := head_card_eq hfin
  have hz : (zeroFinite hfin).toFinset.card = 2 := by omega
  rw [hz]

end KsIndex.DtNCircle
