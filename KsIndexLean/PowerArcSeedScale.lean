module

public import KsIndexLean.PowerArcNormalized
public import KsIndexLean.PowerArcConvolution

@[expose] public section


/-! Natural-number recurrence sums for the two power-arc seed scales. -/

namespace KsIndex.PowerArc

lemma normalized_sq_summable {β : ℝ} (hβ : 0 < β) (r : ℤ) (hr : 0 ≤ r)
    (hg : g β r ≠ 0) :
    Summable (fun n : ℕ => normalizedCoefficient β r n ^ 2) := by
  have hs := (seedScale_summable hβ r).comp_injective Nat.cast_injective
  apply hs.congr
  intro n
  dsimp only [Function.comp_def]
  rw [normalizedCoefficient_eq hβ (by exact_mod_cast hr) hg]
  push_cast
  rw [show (r : ℝ) + 2 * n = 2 * n + r by ring]

lemma seedScale_one {β : ℝ} (hβ : 0 < β) :
    seedScale β 1 = 2 * ∑' n : ℕ, normalizedCoefficient β 1 n ^ 2 := by
  have hg : g β 1 ≠ 0 := (g_pos_of_mem_unit hβ (by norm_num) (by norm_num)).ne'
  have hs := normalized_sq_summable hβ 1 (by norm_num) (by simpa using hg)
  simp only [Int.cast_one] at hs
  have hh := tsum_nat_add_neg_add_one (seedScale_summable hβ 1)
  have hpos : ∀ n : ℕ, (g β (2 * ((n : ℤ) : ℝ) + (1 : ℤ)) / g β (1 : ℤ)) ^ 2 =
      normalizedCoefficient β 1 n ^ 2 := by
    intro n
    rw [normalizedCoefficient_eq hβ (by norm_num) hg]
    push_cast
    rw [show (1 : ℝ) + 2 * n = 2 * n + 1 by ring]
  have hneg : ∀ n : ℕ, (g β (2 * ((-((n : ℤ) + 1)) : ℝ) + (1 : ℤ)) /
      g β (1 : ℤ)) ^ 2 = normalizedCoefficient β 1 n ^ 2 := by
    intro n
    push_cast
    rw [show 2 * (-((n : ℝ) + 1)) + 1 = -(1 + 2 * n) by ring, g_neg,
      normalizedCoefficient_eq hβ (by norm_num) hg]
  change _ = seedScale β 1 at hh
  simp only [hpos] at hh
  push_cast at hh hneg
  simp only [hneg] at hh
  rw [← hh, hs.tsum_add hs]
  ring

lemma seedScale_zero {β : ℝ} (hβ : 0 < β) :
    seedScale β 0 = 2 * (∑' n : ℕ, normalizedCoefficient β 0 n ^ 2) - 1 := by
  have hg : g β 0 ≠ 0 := (g_pos_of_mem_unit hβ (by norm_num) (by norm_num)).ne'
  have hs := normalized_sq_summable hβ 0 (by norm_num) (by simpa using hg)
  simp only [Int.cast_zero] at hs
  have hh := tsum_nat_add_neg_add_one (seedScale_summable hβ 0)
  have hpos : ∀ n : ℕ, (g β (2 * (n : ℝ)) / g β 0) ^ 2 =
      normalizedCoefficient β 0 n ^ 2 := by
    intro n
    rw [normalizedCoefficient_eq hβ (by norm_num) hg]
    simp
  have hneg : ∀ n : ℕ, (g β (2 * (-((n : ℝ) + 1))) / g β 0) ^ 2 =
      normalizedCoefficient β 0 (n + 1) ^ 2 := by
    intro n
    rw [show 2 * (-((n : ℝ) + 1)) = -(2 * ((n : ℝ) + 1)) by ring, g_neg,
      normalizedCoefficient_eq hβ (by norm_num) hg]
    simp
  change _ = seedScale β 0 at hh
  push_cast at hh
  simp only [add_zero, hpos, hneg] at hh
  have hshift : Summable (fun n : ℕ => normalizedCoefficient β 0 (n + 1) ^ 2) :=
    (summable_nat_add_iff 1).mpr hs
  rw [hs.tsum_add hshift] at hh
  have hsplit := hs.tsum_eq_zero_add
  simp only [show normalizedCoefficient β 0 0 = 1 from rfl, one_pow] at hsplit
  linarith

end KsIndex.PowerArc
