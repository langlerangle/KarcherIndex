module

public import KsIndexLean.CircleQ

@[expose] public section


/-! # Opposite-half decomposition of the transpose weight (finite form)

For fixed `n` (`L = 6n+1`) and every `m` (`Lₘ = 6m+4`), the partial fraction
`Lₘ = 3(2(m-n)+1) + L` together with the sign split of `|Lₘ|` rewrites the
transpose weight `sigM m * chat (m-n)` as the diagonal symbol
`sigP n * chat (m-n)`, an opposite-half part, and two moment kernels (the
`Z`- and `V`-type terms). The resulting identity holds over any finite set.
This file proves the algebraic finite-sum statement; convergence and the
passage to infinite sums require separate arguments. -/

noncomputable section
namespace KsIndex.OppositeHalf
open CircleQ Real

/-- `+1` on the half where `L = 6n+1 > 0` (that is, `n ≥ 0`), else `-1`. -/
def oppSign (n : ℤ) : ℝ := if 0 ≤ n then 1 else -1

lemma negOne_zpow_sub (a b : ℤ) : (-1 : ℝ) ^ (a - b) = (-1) ^ a * (-1) ^ b := by
  have h1 : (-1 : ℝ) ^ (2 * b) = 1 := by
    rw [zpow_mul]
    norm_num
  have h2 : (-1 : ℝ) ^ (a - b) * (-1) ^ (2 * b) = (-1) ^ (a + b) := by
    rw [← zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
    congr 1
    ring
  rw [h1, mul_one] at h2
  rw [h2, zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]

lemma freqM_ne_zero (m : ℤ) : (6 * (m : ℝ) + 4) ≠ 0 := by
  have h : ((6 * m + 4 : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
  intro hc
  apply h
  push_cast
  linarith

lemma freqP_ne_zero (n : ℤ) : (6 * (n : ℝ) + 1) ≠ 0 := by
  have h : ((6 * n + 1 : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
  intro hc
  apply h
  push_cast
  linarith

lemma odd_den_ne_zero (m n : ℤ) : (2 * ((m : ℝ) - n) + 1) ≠ 0 := by
  have h : ((2 * (m - n) + 1 : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
  intro hc
  apply h
  push_cast
  linarith

/-- Pointwise partial-fraction split of the transpose weight. -/
lemma pointwise_split (n m : ℤ) :
    sigM m * chat (m - n) =
      sigP n * chat (m - n)
      + 2 * (if (6 * n + 1) * (6 * m + 4) < 0 then sigM m * chat (m - n) else 0)
      + 6 * oppSign n / π * ((-1 : ℝ) ^ m * (-1) ^ n)
      + 24 / (π * |6 * (n : ℝ) + 1|) *
          ((-1 : ℝ) ^ m * (-1) ^ n / (6 * (m : ℝ) + 4)) := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hLm := freqM_ne_zero m
  have hLn := freqP_ne_zero n
  have hd := odd_den_ne_zero m n
  have hcast : ((m - n : ℤ) : ℝ) = (m : ℝ) - n := by push_cast; ring
  simp only [sigM, sigP, chat, oppSign, negOne_zpow_sub, hcast]
  by_cases hn : (0 : ℤ) ≤ n
  · have hLnpos : (0 : ℝ) < 6 * (n : ℝ) + 1 := by
      have h0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    rw [abs_of_pos hLnpos, if_pos hn]
    by_cases hm : (0 : ℤ) ≤ m
    · have hLmpos : (0 : ℝ) < 6 * (m : ℝ) + 4 := by
        have h0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        linarith
      rw [abs_of_pos hLmpos, if_neg (not_lt.mpr (le_of_lt (mul_pos
        (show (0 : ℤ) < 6 * n + 1 by omega) (show (0 : ℤ) < 6 * m + 4 by omega))))]
      field_simp
      ring
    · have hLmneg : 6 * (m : ℝ) + 4 < 0 := by
        have h0 : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
        linarith
      rw [abs_of_neg hLmneg, if_pos (mul_neg_of_pos_of_neg
        (show (0 : ℤ) < 6 * n + 1 by omega) (show 6 * m + 4 < (0 : ℤ) by omega))]
      field_simp
      ring
  · have hLnneg : 6 * (n : ℝ) + 1 < 0 := by
      have h0 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      linarith
    rw [abs_of_neg hLnneg, if_neg hn]
    by_cases hm : (0 : ℤ) ≤ m
    · have hLmpos : (0 : ℝ) < 6 * (m : ℝ) + 4 := by
        have h0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        linarith
      rw [abs_of_pos hLmpos, if_pos (mul_neg_of_neg_of_pos
        (show 6 * n + 1 < (0 : ℤ) by omega) (show (0 : ℤ) < 6 * m + 4 by omega))]
      field_simp
      ring
    · have hLmneg : 6 * (m : ℝ) + 4 < 0 := by
        have h0 : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
        linarith
      rw [abs_of_neg hLmneg, if_neg (not_lt.mpr (le_of_lt (mul_pos_of_neg_of_neg
        (show 6 * n + 1 < (0 : ℤ) by omega) (show 6 * m + 4 < (0 : ℤ) by omega))))]
      field_simp
      ring

/-- ★ The finite opposite-half identity (receipt 2218, finite form): over any
finite index set and any real sequence, the transpose sum decomposes into the
diagonal part, twice the opposite-half part, and the `Z`- and `V`-moment terms. -/
theorem sum_split (n : ℤ) (S : Finset ℤ) (x : ℤ → ℝ) :
    (∑ m ∈ S, sigM m * chat (m - n) * x m) =
      sigP n * (∑ m ∈ S, chat (m - n) * x m)
      + 2 * (∑ m ∈ S.filter fun m => (6 * n + 1) * (6 * m + 4) < 0,
          sigM m * chat (m - n) * x m)
      + 6 * oppSign n / π * (-1 : ℝ) ^ n * (∑ m ∈ S, (-1 : ℝ) ^ m * x m)
      + 24 / (π * |6 * (n : ℝ) + 1|) * (-1 : ℝ) ^ n *
          (∑ m ∈ S, (-1 : ℝ) ^ m * x m / (6 * (m : ℝ) + 4)) := by
  have key : ∀ m ∈ S, sigM m * chat (m - n) * x m =
      sigP n * (chat (m - n) * x m)
      + 2 * (if (6 * n + 1) * (6 * m + 4) < 0
          then sigM m * chat (m - n) * x m else 0)
      + 6 * oppSign n / π * (-1 : ℝ) ^ n * ((-1 : ℝ) ^ m * x m)
      + 24 / (π * |6 * (n : ℝ) + 1|) * (-1 : ℝ) ^ n *
          ((-1 : ℝ) ^ m * x m / (6 * (m : ℝ) + 4)) := by
    intro m _
    have h := pointwise_split n m
    by_cases hc : (6 * n + 1) * (6 * m + 4) < 0
    · rw [if_pos hc] at h
      rw [if_pos hc]
      linear_combination (x m) * h
    · rw [if_neg hc] at h
      rw [if_neg hc]
      linear_combination (x m) * h
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_filter]

end KsIndex.OppositeHalf
