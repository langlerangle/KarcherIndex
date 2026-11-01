module

/-
KsIndexLean — SeamNat: the pure-Neumann seam identity `SeamBridge.pureN` on the natural spaces,
every rotation class.

Combining the seam estimates — for `k ≥ 3` and every class `r < k`:
  `formIndex (Qd k) (NatCc k true true ⊓ Erot1 k r) = neumannCount k r + [r ≡ 0]`.
* `≤` is `SeamUpper.seamNat_le_neumannCount` (the trace-coefficient map);
* `≥` for `r ≢ 0` is `SeamLowerCount.neumannCount_le_seamNat` (the cut-off modes);
* `≥` for `r ≡ 0` is `SeamLowerZero.one_le_seamNat_zero` (the `ℓ = 0` cut-off constant).

This is the value of the `pureN` field of `SeamBridge` on the natural test spaces; transport to `SeamBridge.pureN` on `SingleCc` uses `ArcEncodingDensity` transport.
-/
public import KsIndexLean.SeamUpper
public import KsIndexLean.SeamLowerZero

@[expose] public section


noncomputable section

open Complex
open KsIndex.FormIndex KsIndex.SingleDiskBridge

namespace KsIndex.SingleDisk

variable {k : ℕ}

/-- **The pure-Neumann seam identity on the natural spaces** (`k ≥ 3`, every class `r < k`):
`ind(Qd k) = neumannCount k r + [r ≡ 0]`.  This is `SeamBridge.pureN` on `NatCc`. -/
theorem seamNat_eq (hk : 3 ≤ k) {r : ℕ} (hr : r < k) :
    formIndex (Qd k) (NatCc k true true ⊓ Erot1 k r)
      = neumannCount k (r : ZMod k) + (if (r : ZMod k) = 0 then 1 else 0) := by
  refine le_antisymm (KsIndex.SeamUpper.seamNat_le_neumannCount hk hr) ?_
  by_cases hr0 : (r : ZMod k) = 0
  · haveI : NeZero k := ⟨by omega⟩
    have hrz : r = 0 := by
      have hv : (r : ZMod k).val = r := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hr]
      rw [← hv, hr0, ZMod.val_zero]
    subst hrz
    simp only [Nat.cast_zero] at hr0 ⊢
    rw [neumannCount_zero hk, if_pos hr0, zero_add]
    exact one_le_seamNat_zero hk
  · rw [if_neg hr0, add_zero]
    exact neumannCount_le_seamNat hk hr

end KsIndex.SingleDisk
