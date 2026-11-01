module

/-
The m=2 index formula: `indSurface k 2 = 4k - 3` for `k >= 3`,
under the explicit hypothesis `EncodingDensity k`.

For each rotation class `r < k`, the natural seam-cell indices are DD = 0,
DN = 1, and NN = `neumannCount + [r = 0]`. The NN class sum is `2k - 3`,
so summing `DD + 2*DN + NN` gives `4k - 3`.

This module assembles the index formula from those cell counts and
`TwistAssembly.indSurface_two_eq_DN`; it does not discharge `EncodingDensity`
or supply the nullity formula.
-/
public import KsIndexLean.TwistAssembly
public import KsIndexLean.SeamNat
public import KsIndexLean.SeamPureD
public import KsIndexLean.SeamLowerMixed
public import KsIndexLean.MixedClassZeroBracketing

@[expose] public section


noncomputable section

open KsIndex.Surface KsIndex.SingleDisk KsIndex.SingleDiskBridge KsIndex.FormIndex
  KsIndex.TwistSwap

namespace KsIndex.Capstone

variable {k : ℕ}

/-! ### The census rows, packaged per cell -/

/-- The pure-Dirichlet cell index is zero. -/
lemma seamNat_FF (hk : 3 ≤ k) (r : ℕ) : seamNat k false false r = 0 :=
  seamNat_pureD hk r

/-- The mixed cell index is one in every class `r < k`. The zero class is obtained
from the Dirichlet strict-bracketing route (`mixed_class_zero_pair_bracketing_uncond`,
transferred through `mixedCharacter_weak_index_eq_seamNat`); positive classes use
`seamNat_mixed_eq_one`. -/
lemma seamNat_TF_eq_one (hk : 3 ≤ k) {r : ℕ} (hr : r < k) :
    seamNat k true false r = 1 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr1
  · rw [← KsIndex.Spectral.mixedCharacter_weak_index_eq_seamNat (by omega : (2:ℕ) ≤ k) 0 true false]
    exact (KsIndex.Spectral.mixed_class_zero_pair_bracketing_uncond hk (by decide)).1
  · exact KsIndex.SeamLowerMixed.seamNat_mixed_eq_one hk hr1 (by omega)

/-- The NN cell value as a natural number: `[1 ≤ r ≤ k−2] + [2 ≤ r] + [r = 0]`. -/
def ttVal (k r : ℕ) : ℕ :=
  (if 1 ≤ r ∧ r ≤ k - 2 then 1 else 0) + (if 2 ≤ r then 1 else 0) + (if r = 0 then 1 else 0)

/-- The pure-Neumann cell index in natural-number form, with the `ZMod`
conditions rewritten using `r < k`. -/
lemma seamNat_TT_eq (hk : 3 ≤ k) {r : ℕ} (hr : r < k) :
    seamNat k true true r = ((ttVal k r : ℕ) : ℕ∞) := by
  have : NeZero k := ⟨by omega⟩
  have hval : (r : ZMod k).val = r := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hr]
  have hz : ((r : ZMod k) = 0) ↔ r = 0 := by
    constructor
    · intro h0
      have h := hval
      rw [h0, ZMod.val_zero] at h
      omega
    · rintro rfl
      exact Nat.cast_zero
  have h := seamNat_eq hk hr
  unfold seamNat
  rw [h, KsIndex.SingleDiskBridge.neumannCount_eq hk, hval]
  simp only [hz]
  have hif : (if r = 0 then (1 : ℕ∞) else 0) = ((if r = 0 then 1 else 0 : ℕ) : ℕ∞) := by
    split_ifs <;> simp
  rw [hif, ← Nat.cast_add]
  rfl

/-! ### The class sums -/

/-- The NN column sums to `2k − 3`: the two indicator windows contribute `k − 2` each
(`r ∈ [1, k−2]` and `r ∈ [2, k−1]`), the `r = 0` tanh mode contributes `1`. -/
lemma sum_ttVal (hk : 3 ≤ k) : ∑ r ∈ Finset.range k, ttVal k r = 2 * k - 3 := by
  unfold ttVal
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h1 : (Finset.range k).filter (fun r => 1 ≤ r ∧ r ≤ k - 2) = Finset.Icc 1 (k - 2) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  have h2 : (Finset.range k).filter (fun r => 2 ≤ r) = Finset.Icc 2 (k - 1) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  have h3 : (Finset.range k).filter (fun r => r = 0) = {0} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    omega
  rw [Finset.sum_boole, Finset.sum_boole, Finset.sum_boole, h1, h2, h3,
    Nat.card_Icc, Nat.card_Icc, Finset.card_singleton]
  simp only [Nat.cast_id]
  omega

/-! ### The capstone -/

/-- The m=2 index formula: `ind(Ξ_{k,2}) = 4k − 3` for every `k ≥ 3`, under the single
named hypothesis `EncodingDensity k` — the paper's Theorem for `m = 2` (index half),
[ksindexi] §1/§5. -/
theorem indSurface_two_val (hk : 3 ≤ k) (hE : EncodingDensity k) :
    indSurface k 2 = ((4 * k - 3 : ℕ) : ℕ∞) := by
  have hcell : ∀ r : Fin k,
      seamNat k false false (r : ℕ) + 2 * seamNat k true false (r : ℕ)
        + seamNat k true true (r : ℕ)
      = ((2 + ttVal k (r : ℕ) : ℕ) : ℕ∞) := by
    intro r
    rw [seamNat_FF hk, seamNat_TF_eq_one hk r.isLt, seamNat_TT_eq hk r.isLt,
      mul_one, zero_add]
    push_cast
    rfl
  rw [indSurface_two_eq_DN (by omega) hE, Finset.sum_congr rfl (fun r _ => hcell r),
    ← Nat.cast_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun r => 2 + ttVal k r) k, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_range, smul_eq_mul, sum_ttVal hk]
  omega

/-- The index half of `Theorem_m2` (SurfaceTargets), under the encoding hypothesis for
every `k`. -/
theorem theorem_m2_index (hE : ∀ k, 3 ≤ k → EncodingDensity k) :
    ∀ k, 3 ≤ k → indSurface k 2 = ((4 * k - 3 : ℕ) : ℕ∞) :=
  fun _ hk => indSurface_two_val hk (hE _ hk)

end KsIndex.Capstone
