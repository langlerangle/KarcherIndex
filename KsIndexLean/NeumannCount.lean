module

/-
# The class-refined Neumann count `neumannCount k c` in closed form

For `3 ≤ k`, `neumannCount k c = formIndex (Qdiag (dtnSymbolClass k c)) (DomDiag (dtnSymbolClass k c))` counts
the negative DtN modes `ℓ ≠ 0`, `|ℓ| ≤ k−2`, in the rotation class `ℓ ≡ c (mod k)`.  The window
`[−(k−2), k−2]` meets each residue class `c` in the integers `c.val` (when `1 ≤ c.val ≤ k−2`) and
`c.val − k` (when `2 ≤ c.val`), so

  `neumannCount k c = [1 ≤ c.val ≤ k−2] + [2 ≤ c.val]`,

i.e. `0` for `c = 0`, `1` for `c = ±1`, `2` for `2 ≤ c.val ≤ k−2`; summing over `c` gives
`2k − 4 = ind(nop_k)` (`nop_index`).  This is the nonzero-mode contribution used by `SeamBridge.pureN`.
-/
public import Mathlib
public import KsIndexLean.SingleDiskBridge

@[expose] public section


namespace KsIndex.SingleDiskBridge

open KsIndex.FormIndex KsIndex.DiagForm KsIndex.DtNCircle

variable {k : ℕ}

/-- The residue-class condition on the window: an integer of absolute value `≤ k−2` is `≡ c` iff
it is `c.val` or `c.val − k`. -/
lemma window_class_iff (hk : 3 ≤ k) (c : ZMod k) {ℓ : ℤ} (hℓ : |ℓ| ≤ (k : ℤ) - 2) :
    ((ℓ : ZMod k) = c) ↔ (ℓ = c.val ∨ ℓ = c.val - k) := by
  have : NeZero k := ⟨by omega⟩
  have hcv : c.val < k := ZMod.val_lt c
  rw [show ((ℓ : ZMod k) = c) ↔ ((ℓ : ZMod k) = ((c.val : ℤ) : ZMod k)) by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val], ZMod.intCast_eq_intCast_iff_dvd_sub]
  have hb := abs_le.mp hℓ
  constructor
  · rintro ⟨t, ht⟩
    have hk' : (3 : ℤ) ≤ k := by exact_mod_cast hk
    have hcv' : (c.val : ℤ) < k := by exact_mod_cast hcv
    have ht0 : 0 ≤ t := by
      by_contra h
      push Not at h
      nlinarith
    have ht1 : t ≤ 1 := by
      by_contra h
      push Not at h
      nlinarith
    rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl)
    · exact ⟨0, by ring⟩
    · exact ⟨1, by ring⟩

/-- Finiteness of the class-`c` head set. -/
lemma dtnClass_head_finite (hk : 3 ≤ k) (c : ZMod k) :
    {ℓ : NZ | dtnSymbolClass k c ℓ ≤ 0}.Finite := by
  apply (dtn_head_finite hk).subset
  intro ℓ hℓ
  simp only [Set.mem_ofPred_eq, dtnSymbolClass] at hℓ ⊢
  split_ifs at hℓ with h
  · exact hℓ
  · norm_num at hℓ

/-- **`neumannCount` in closed form**: `[1 ≤ c.val ≤ k−2] + [2 ≤ c.val]`. -/
theorem neumannCount_eq (hk : 3 ≤ k) (c : ZMod k) :
    neumannCount k c =
      (((if 1 ≤ c.val ∧ c.val ≤ k - 2 then 1 else 0)
        + (if 2 ≤ c.val then 1 else 0) : ℕ) : ℕ∞) := by
  have : NeZero k := ⟨by omega⟩
  have hcv : c.val < k := ZMod.val_lt c
  have hfin := dtnClass_head_finite hk c
  unfold neumannCount
  rw [formIndex_Qdiag hfin]
  congr 1
  -- the negative set, as a subtype finset of an explicit finset of integers
  set T : Finset ℤ := ({(c.val : ℤ), (c.val : ℤ) - k} : Finset ℤ).filter
    (fun ℓ => |ℓ| ≤ (k : ℤ) - 2) with hT
  have hset : (negFinite hfin).toFinset = T.subtype (· ≠ 0) := by
    ext ℓ
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_subtype, hT, Finset.mem_filter,
      Finset.mem_insert, Finset.mem_singleton, dtnSymbolClass]
    split_ifs with h
    · rw [dtn_lt_zero_iff (by omega)]
      constructor
      · intro hℓ; exact ⟨(window_class_iff hk c hℓ).mp h, hℓ⟩
      · exact fun hℓ => hℓ.2
    · constructor
      · intro h1; norm_num at h1
      · rintro ⟨h1, h2⟩; exact absurd ((window_class_iff hk c h2).mpr h1) h
  rw [hset, Finset.card_subtype, hT, Finset.filter_filter]
  have hne : (c.val : ℤ) ≠ (c.val : ℤ) - k := by omega
  rw [Finset.filter_insert, Finset.filter_singleton]
  have hk' : (3 : ℤ) ≤ k := by exact_mod_cast hk
  have hcv' : (c.val : ℤ) < k := by exact_mod_cast hcv
  have hcv0 : (0 : ℤ) ≤ c.val := by exact_mod_cast Nat.zero_le _
  have e1 : (|(c.val : ℤ)| ≤ (k : ℤ) - 2 ∧ (c.val : ℤ) ≠ 0)
      ↔ (1 ≤ c.val ∧ c.val ≤ k - 2) := by
    rw [abs_le]; omega
  have e2 : (|(c.val : ℤ) - k| ≤ (k : ℤ) - 2 ∧ (c.val : ℤ) - k ≠ 0) ↔ 2 ≤ c.val := by
    rw [abs_le]; omega
  simp only [e1, e2]
  split_ifs with h1 h2 h2
  · rw [Finset.card_pair hne]
  · simp
  · simp
  · simp

/-- `c = 0`: no negative modes (the `ℓ = 0` tanh mode is counted separately in
`SeamBridge.pureN`). -/
theorem neumannCount_zero (hk : 3 ≤ k) : neumannCount k 0 = 0 := by
  have : NeZero k := ⟨by omega⟩
  rw [neumannCount_eq hk, ZMod.val_zero]; simp

/-- `c = 1`: exactly one negative mode (`ℓ = 1`). -/
theorem neumannCount_one (hk : 3 ≤ k) : neumannCount k 1 = 1 := by
  have : Fact (1 < k) := ⟨by omega⟩
  rw [neumannCount_eq hk, ZMod.val_one]
  have : ¬ (2 ≤ 1) := by omega
  simp [this, show 1 ≤ k - 2 by omega]

/-- `c = −1`: exactly one negative mode (`ℓ = −1`). -/
theorem neumannCount_neg_one (hk : 3 ≤ k) : neumannCount k (-1) = 1 := by
  have : Fact (1 < k) := ⟨by omega⟩
  have hv : ((-1 : ZMod k)).val = k - 1 := by
    rw [ZMod.neg_val, if_neg one_ne_zero, ZMod.val_one]
  rw [neumannCount_eq hk, hv]
  have h1 : ¬ (k - 1 ≤ k - 2) := by omega
  simp [h1, show 2 ≤ k - 1 by omega]

/-- `2 ≤ c.val ≤ k−2`: two negative modes (`ℓ = c.val` and `ℓ = c.val − k`). -/
theorem neumannCount_two (hk : 3 ≤ k) (c : ZMod k) (h2 : 2 ≤ c.val) (hk2 : c.val ≤ k - 2) :
    neumannCount k c = 2 := by
  rw [neumannCount_eq hk]
  simp [h2, hk2, show 1 ≤ c.val by omega]

end KsIndex.SingleDiskBridge
