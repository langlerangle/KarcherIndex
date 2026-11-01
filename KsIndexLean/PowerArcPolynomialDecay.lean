module

public import KsIndexLean.PowerArcSignedTails
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section


/-! Polynomial decay from the exact two-step power-arc recurrence. -/
namespace KsIndex.PowerArc

lemma polynomial_decay_ratio {β x : ℝ} (hβ : (2/5 : ℝ) ≤ β)
    (hβ1 : β ≤ 1) (hx : 32 ≤ x) :
    (x-β) * (1+2/x)^(11/8 : ℝ) ≤ x+β+2 := by
  have hx0 : 0 < x := by linarith
  have ht0 : 0 ≤ 2/x := by positivity
  have hb := rpow_one_add_le_one_add_mul_self
    (by linarith : (-1 : ℝ) ≤ 2/x) (by norm_num : (0 : ℝ) ≤ 3/8)
    (by norm_num : (3/8 : ℝ) ≤ 1)
  have he : (1+2/x)^(11/8 : ℝ) = (1+2/x) * (1+2/x)^(3/8 : ℝ) := by
    rw [show (11/8 : ℝ) = 1 + 3/8 by norm_num, Real.rpow_add (by positivity)]
    simp
  rw [he]
  calc
    _ ≤ (x-β) * ((1+2/x) * (1+(3/8 : ℝ)*(2/x))) := by
      gcongr
      linarith
    _ ≤ (x-(2/5 : ℝ)) * ((1+2/x) * (1+(3/8 : ℝ)*(2/x))) := by
      gcongr
    _ ≤ x+(2/5 : ℝ)+2 := by
      apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hx0)).mp
      field_simp
      nlinarith [sq_nonneg (x-16)]
    _ ≤ x+β+2 := by linarith

/-- The weighted magnitude decreases along the two-step recurrence in the tail. -/
lemma weighted_abs_g_step {β x : ℝ} (hβ : (2/5 : ℝ) ≤ β)
    (hβ1 : β ≤ 1) (hx : 32 ≤ x) :
    (x+2)^(11/8 : ℝ) * |g β (x+2)| ≤ x^(11/8 : ℝ) * |g β x| := by
  have hx0 : 0 < x := by linarith
  have hβ0 : 0 < β := by linarith
  have hd : 0 < x+β+2 := by linarith
  have hrec := abs_g_step hβ0 (by linarith : β ≤ x)
  have hp : (x+2)^(11/8 : ℝ) = x^(11/8 : ℝ) * (1+2/x)^(11/8 : ℝ) := by
    rw [← Real.mul_rpow hx0.le (by positivity : 0 ≤ 1+2/x)]
    congr 1
    field_simp
  apply (mul_le_mul_iff_right₀ hd).mp
  calc
    _ = (x+2)^(11/8 : ℝ) * ((x+β+2) * |g β (x+2)|) := by ring
    _ = (x+2)^(11/8 : ℝ) * ((x-β) * |g β x|) := by rw [hrec]
    _ = (x^(11/8 : ℝ) * ((x-β)*(1+2/x)^(11/8 : ℝ))) * |g β x| := by rw [hp]; ring
    _ ≤ (x^(11/8 : ℝ) * (x+β+2)) * |g β x| := by
      gcongr
      exact polynomial_decay_ratio hβ hβ1 hx
    _ = _ := by ring

/-- Each parity tail is bounded by its first weighted coefficient. -/
theorem weighted_abs_g_tail {β r : ℝ} (hβ : (2/5 : ℝ) ≤ β)
    (hβ1 : β ≤ 1) (hr : 32 ≤ r) (n : ℕ) :
    (r+2*n)^(11/8 : ℝ) * |g β (r+2*n)| ≤ r^(11/8 : ℝ) * |g β r| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := weighted_abs_g_step hβ hβ1
      (show 32 ≤ r+2*n by linarith [Nat.cast_nonneg (α := ℝ) n])
    simpa only [Nat.cast_add, Nat.cast_one, mul_add, mul_one, add_assoc] using hs.trans ih

/-- A finite initial segment controls all nonnegative integer frequencies. -/
theorem weighted_abs_g_nat {β : ℝ} (hβ : (2/5 : ℝ) ≤ β) (hβ1 : β ≤ 1)
    (n : ℕ) :
    (n : ℝ)^(11/8 : ℝ) * |g β n| ≤
      ∑ k ∈ Finset.range 34, (k : ℝ)^(11/8 : ℝ) * |g β k| := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 34
    · exact Finset.single_le_sum (f := fun k : ℕ => (k : ℝ)^(11/8 : ℝ) * |g β k|) (fun k _ => mul_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg k) _) (abs_nonneg _)) (Finset.mem_range.mpr hn)
    · have hprev := ih (n-2) (by omega)
      have hs := weighted_abs_g_step hβ hβ1
        (show (32 : ℝ) ≤ ((n-2 : ℕ) : ℝ) by exact_mod_cast (show 32 ≤ n-2 by omega))
      have he : ((n-2 : ℕ) : ℝ) + 2 = (n : ℝ) := by
        exact_mod_cast (show n-2+2 = n by omega)
      rw [he] at hs
      exact hs.trans hprev

/-- Including the zero frequency gives a uniform polynomially weighted bound. -/
theorem exists_nat_weight_bound {β : ℝ} (hβ : (2/5 : ℝ) ≤ β) (hβ1 : β ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (1+(n:ℝ))^(11/8 : ℝ) * |g β n| ≤ C := by
  let K : ℝ := ∑ k ∈ Finset.range 34, (k : ℝ)^(11/8 : ℝ) * |g β k|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun k _ => mul_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg k) _) (abs_nonneg _))
  refine ⟨|g β 0| + (2 : ℝ)^(11/8 : ℝ)*K, by positivity, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, add_zero, Real.one_rpow, one_mul]
    linarith [mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (11/8)) hK]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    have hp := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 1+(n:ℝ))
      (by linarith : 1+(n:ℝ) ≤ 2*(n:ℝ)) (by norm_num : (0 : ℝ) ≤ 11/8)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg n)] at hp
    calc
      _ ≤ ((2 : ℝ)^(11/8 : ℝ)*(n:ℝ)^(11/8 : ℝ))*|g β n| :=
        mul_le_mul_of_nonneg_right hp (abs_nonneg _)
      _ = (2 : ℝ)^(11/8 : ℝ)*((n:ℝ)^(11/8 : ℝ)*|g β n|) := by ring
      _ ≤ (2 : ℝ)^(11/8 : ℝ)*K := mul_le_mul_of_nonneg_left
        (weighted_abs_g_nat hβ hβ1 n) (by positivity)
      _ ≤ _ := le_add_of_nonneg_left (abs_nonneg _)

end KsIndex.PowerArc
