module

/-
# Exact reindexing of the disk and single-arc symbols

For `k ≥ 1`, `1 ≤ r ≤ k-1` and `n : ℤ`, `sigma_natAbs_eq` proves
`σ_k(|kn+r|) = k · sigmaArc (aOf (k-r) k) (bOf k) n`.
The parameters satisfy `aOf (k-r) k = r/k` and `bOf k = (k-1)/k`.
The residue-class assumptions ensure that `kn+r` is nonzero, so its natural
absolute value is a positive disk mode.

This is the symbol identity used in the paper's `single-arc_reduction`:
the surface rotation class `r` corresponds to the arc class `j = k-r`.
Since `k` is positive, the identity preserves the sign of each symbol.
Reindexing coefficient sums and transporting function-space domains require
separate results; this module proves the pointwise algebraic identity.
-/
public import KsIndexLean.RadialMode
public import KsIndexLean.ArcForm
public import KsIndexLean.ArcLower

@[expose] public section


noncomputable section

open KsIndex.Radial KsIndex.ArcForm KsIndex.ArcLower

namespace KsIndex.Reindex

variable {k r : ℕ}

/-- The arc parameter of surface class `r` is `r/k`: `aOf (k−r) k = r/k`. -/
lemma aOf_sub_eq (hk : 1 ≤ k) (hrk : r ≤ k) : aOf (k - r) k = (r : ℝ) / k := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hk
  rw [aOf, Nat.cast_sub hrk]
  field_simp
  ring

/-- The arc parameter `b = 1 − 1/k` is `κ/k`. -/
lemma bOf_eq_kap (hk : 1 ≤ k) : bOf k = kap k / k := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hk
  rw [bOf, kap]
  field_simp

/-- The mode index `kn + r` never vanishes when `1 ≤ r ≤ k−1` (it is `≡ r ≢ 0 (mod k)`). -/
lemma add_mul_ne_zero (hr1 : 1 ≤ r) (hrk : r ≤ k - 1) (n : ℤ) :
    (k : ℤ) * n + r ≠ 0 := by
  intro h
  have hdvd : (k : ℤ) ∣ (r : ℤ) := ⟨-n, by linear_combination h⟩
  have hrpos : 0 < (r : ℤ) := by exact_mod_cast hr1
  have hle : (k : ℤ) ≤ (r : ℤ) := Int.le_of_dvd hrpos hdvd
  have hrltk : r < k := by omega
  have hrltk' : (r : ℤ) < (k : ℤ) := by exact_mod_cast hrltk
  linarith

/-- **The exact single-arc symbol identity.**  For a surface rotation class `r`
(`1 ≤ r ≤ k−1`) and mode `ℓ = kn + r`, the disk DtN symbol is `k` times the circle arc symbol at
`a = aOf (k−r) k = r/k`, `b = bOf k`:

  `sigma k |kn + r| = k · sigmaArc (aOf (k−r) k) (bOf k) n`.

The positive factor `k` transports negativity in both directions (the paper's
`single-arc_reduction`). -/
theorem sigma_natAbs_eq (hk : 1 ≤ k) (hr1 : 1 ≤ r) (hrk : r ≤ k - 1) (n : ℤ) :
    sigma k ((k : ℤ) * n + r).natAbs
      = (k : ℝ) * sigmaArc (aOf (k - r) k) (bOf k) n := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hrk' : r ≤ k := le_trans hrk (Nat.sub_le k 1)
  set K : ℤ := (k : ℤ) * n + r with hKdef
  have hKne : K ≠ 0 := add_mul_ne_zero hr1 hrk n
  have hKRne : (K : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hKne
  have hKabs : ((K.natAbs : ℝ)) = |(K : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have hKR : (K : ℝ) = (k : ℝ) * (n : ℝ) + (r : ℝ) := by rw [hKdef]; push_cast; ring
  have habspos : 0 < |(K : ℝ)| := abs_pos.mpr hKRne
  have hAbs0 : |(K : ℝ)| ≠ 0 := ne_of_gt habspos
  have hAsq : |(K : ℝ)| ^ 2 = (K : ℝ) ^ 2 := sq_abs _
  have harg : (n : ℝ) + (r : ℝ) / k = (K : ℝ) / k := by rw [hKR]; field_simp
  rw [aOf_sub_eq hk hrk', bOf_eq_kap hk, sigma, sigmaArc, hKabs, harg, abs_div,
    abs_of_pos hkpos, hAsq]
  field_simp

end KsIndex.Reindex
