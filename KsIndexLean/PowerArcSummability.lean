module

public import KsIndexLean.PowerArcRecurrence

@[expose] public section


/-! Weighted summability on the integer frequency lattice for power-arc fields. -/
noncomputable section
namespace KsIndex.PowerArc
open Real

lemma nat_weighted_summable {β : ℝ} (hβ : 0 < β) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * g β n ^ 2) := by
  apply Summable.even_add_odd
  · apply (summable_nat_add_iff 1).mp
    have hw := (weighted_summable_and_bound hβ (r := 2) (by norm_num)).1
    have hu := (unweighted_summable_and_bound hβ (r := 2) (by norm_num)).1
    convert! hw.add hu using 1
    funext n
    push_cast
    rw [show 2 * ((n : ℝ) + 1) = 2 + 2 * n by ring]
    ring
  · have hw := (weighted_summable_and_bound hβ (r := 1) (by norm_num)).1
    have hu := (unweighted_summable_and_bound hβ (r := 1) (by norm_num)).1
    convert! hw.add hu using 1
    funext n
    push_cast
    rw [show 2 * (n : ℝ) + 1 = 1 + 2 * n by ring]
    ring

lemma int_weighted_summable {β : ℝ} (hβ : 0 < β) :
    Summable (fun n : ℤ => (|(n : ℝ)| + 1) * g β n ^ 2) := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · simpa only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using
      nat_weighted_summable hβ
  · simpa only [Int.cast_neg, Int.cast_natCast, abs_neg, g_neg,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using nat_weighted_summable hβ

lemma lattice_weight_bound (d : ℤ) (a : ℝ) (n : ℤ) :
    |6 * (n : ℝ) + a| ≤ (3 + |a - 3 * (d : ℝ)|) * (|2 * (n : ℝ) + d| + 1) := by
  have h := abs_add_le (3 * (2 * (n : ℝ) + d)) (a - 3 * (d : ℝ))
  rw [show 3 * (2 * (n : ℝ) + d) + (a - 3 * (d : ℝ)) = 6 * n + a by ring,
    abs_mul, abs_of_pos (show (0 : ℝ) < 3 by norm_num)] at h
  nlinarith [abs_nonneg (2 * (n : ℝ) + d), abs_nonneg (a - 3 * (d : ℝ))]

/-- All integer translates needed for finite trigonometric trial fields have
finite weighted input and output coefficient energy. -/
theorem lattice_weighted_summable {β : ℝ} (hβ : 0 < β) (d : ℤ) (a : ℝ) :
    Summable (fun n : ℤ => |6 * (n : ℝ) + a| * g β (2 * (n : ℝ) + d) ^ 2) := by
  have hs := (int_weighted_summable hβ).comp_injective
    (show Function.Injective (fun n : ℤ => 2 * n + d) from fun _ _ h => by dsimp at h; omega)
  simp only [Function.comp_def, Int.cast_add, Int.cast_mul, Int.cast_ofNat] at hs
  have hsum : Summable (fun n : ℤ => (3 + |a - 3 * (d : ℝ)|) *
      ((|2 * (n : ℝ) + d| + 1) * g β (2 * (n : ℝ) + d) ^ 2)) := by
    exact hs.mul_left (3 + |a - 3 * (d : ℝ)|)
  apply hsum.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (sq_nonneg _))
  intro n
  have h := mul_le_mul_of_nonneg_right (lattice_weight_bound d a n)
    (sq_nonneg (g β (2 * (n : ℝ) + d)))
  simpa only [mul_assoc] using h

lemma lattice_sq_summable {β : ℝ} (hβ : 0 < β) (d : ℤ) :
    Summable (fun n : ℤ => g β (2 * (n : ℝ) + d) ^ 2) := by
  have hs := (int_weighted_summable hβ).comp_injective
    (show Function.Injective (fun n : ℤ => 2 * n + d) from fun _ _ h => by dsimp at h; omega)
  simp only [Function.comp_def, Int.cast_add, Int.cast_mul, Int.cast_ofNat] at hs
  apply hs.of_nonneg_of_le (fun n => sq_nonneg _)
  intro n
  exact le_mul_of_one_le_left (sq_nonneg _) (by linarith [abs_nonneg (2 * (n : ℝ) + d)])

end KsIndex.PowerArc
