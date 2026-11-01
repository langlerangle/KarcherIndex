module

/-
KsIndexLean — ArcMain: **Theorem m=2 at the circle level.**

For every `k ≥ 3` and `1 ≤ j ≤ k−1`, with `a = 1 − j/k` and `b = 1 − 1/k`,

    `ind_DN(N_{(a;k)}) = 1`   and   `nul_DN(N_{(a;k)}) = 0`

on the arc-supported space `H^{1/2}_{DN;1}(S¹)` (`ArcDom`) — the right-hand sides of
[ksindexi] `single-arc_reduction`, i.e. `Zclasses` after the geometric reduction
`z-reduction`. These are mixed-boundary circle counts, not the nullity of
the whole surface. The full m=2 surface theorem has index `4k − 3` and
nullity `3`, including the translation fields.

Proof: lower bound `ArcLower.one_le_indArc` (the Catalan test field, every class);
upper bound `ind + nul ≤ 1` — edge classes `j ∈ {1, k−1}` via the vanishing head
symbol (`ArcUpperEdge`, using the circle-level form),
interior classes via the paper's `Q-lower`/`Zclasses` argument (`ArcUpper`).
-/
public import KsIndexLean.ArcLower
public import KsIndexLean.ArcUpper

@[expose] public section


noncomputable section

namespace KsIndex.ArcMain

open KsIndex.ArcForm KsIndex.ArcLower KsIndex.ArcUpper KsIndex.ArcEstimate Real

/-- The edge class `j = 1`: `a = b`, so `σ(0) = 0`. -/
lemma sigma_zero_eq_zero_of_j_one (hk : 3 ≤ k) :
    sigmaArc (aOf 1 k) (bOf k) 0 = 0 := by
  have ha := aOf_mem hk le_rfl (by omega)
  rw [sigma_zero_eq ha]
  have : aOf 1 k = bOf k := by
    rw [aOf, bOf]; push_cast; ring
  rw [this, sub_self, zero_div]

/-- The edge class `j = k−1`: `1 − a = b`, so `σ(−1) = 0`. -/
lemma sigma_neg_one_eq_zero_of_j_top (hk : 3 ≤ k) :
    sigmaArc (aOf (k - 1) k) (bOf k) (-1) = 0 := by
  have ha := aOf_mem hk (by omega) le_rfl
  rw [sigma_neg_one_eq ha]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have : 1 - aOf (k - 1) k = bOf k := by
    rw [aOf, bOf]
    have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [this]
    field_simp
    ring
  rw [this, sub_self, zero_div]

/-- Interior classes: `a < b` and `1 − a < b`. -/
lemma interior_of (hk : 3 ≤ k) (hj2 : 2 ≤ j) (hjk : j ≤ k - 2) :
    aOf j k < bOf k ∧ 1 - aOf j k < bOf k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hj2r : (2 : ℝ) ≤ j := by exact_mod_cast hj2
  have hjkr : (j : ℝ) + 2 ≤ k := by exact_mod_cast (show j + 2 ≤ k by omega)
  rw [aOf, bOf]
  constructor
  · rw [sub_lt_sub_iff_left, div_lt_div_iff_of_pos_right hkpos]; linarith
  · rw [sub_sub_cancel, div_lt_iff₀ hkpos, sub_mul, one_mul, div_mul_cancel₀ _ hkpos.ne']
    linarith

/-- **`ind + nul ≤ 1` for every class** `k ≥ 3`, `1 ≤ j ≤ k−1`. -/
theorem indArc_add_nulArc_le_one (hk : 3 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1) :
    indArc (aOf j k) (bOf k) + nulArc (aOf j k) (bOf k) ≤ 1 := by
  have ha := aOf_mem hk hj1 hjk
  have hb := bOf_abs_lt hk
  rcases Nat.lt_or_ge j 2 with h1 | h2
  · -- j = 1
    have : j = 1 := by omega
    subst this
    exact indArc_add_nulArc_le_one_of_sigma_zero ha hb (sigma_zero_eq_zero_of_j_one hk)
  · rcases Nat.lt_or_ge (k - 2) j with htop | hint
    · -- j = k − 1
      have : j = k - 1 := by omega
      subst this
      exact indArc_add_nulArc_le_one_of_sigma_neg_one ha hb (sigma_neg_one_eq_zero_of_j_top hk)
    · -- 2 ≤ j ≤ k − 2
      obtain ⟨hab, hab'⟩ := interior_of hk h2 hint
      exact indArc_add_nulArc_le_one_interior ha hb hab hab'

/-- **Theorem m=2 at the circle level** ([ksindexi] `Zclasses`, right-hand sides of
`single-arc_reduction`): for all `k ≥ 3`, `1 ≤ j ≤ k−1`,
`ind_DN(N_{(1−j/k;k)}) = 1` and `nul_DN(N_{(1−j/k;k)}) = 0`. -/
theorem m2_circle (hk : 3 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1) :
    indArc (aOf j k) (bOf k) = 1 ∧ nulArc (aOf j k) (bOf k) = 0 := by
  have hlow := one_le_indArc hk hj1 hjk
  have hup := indArc_add_nulArc_le_one hk hj1 hjk
  have hind_le : indArc (aOf j k) (bOf k) ≤ 1 := le_trans le_self_add hup
  have hind : indArc (aOf j k) (bOf k) = 1 := le_antisymm hind_le hlow
  refine ⟨hind, ?_⟩
  rw [hind] at hup
  have : nulArc (aOf j k) (bOf k) ≤ 0 := by
    have h' : (1 : ℕ∞) + nulArc (aOf j k) (bOf k) ≤ 1 + 0 := by simpa using hup
    exact (ENat.add_le_add_iff_left ENat.one_ne_top).mp h'
  exact le_antisymm this bot_le

end KsIndex.ArcMain
