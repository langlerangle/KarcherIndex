module

public import KsIndexLean.PowerArcNormalized

@[expose] public section


/-! Error propagation for rounded coefficient recurrence certificates. -/

namespace KsIndex.PowerArc

lemma recurrence_factor_abs_le_one {β r : ℝ} (hβ : 0 < β) (hr : 0 ≤ r) (n : ℕ) :
    |(β - (r + 2 * n)) / (r + 2 * n + β + 2)| ≤ 1 := by
  have hd : 0 < r + 2 * n + β + 2 := by positivity
  rw [abs_div, abs_of_pos hd, div_le_one hd]
  apply abs_le.mpr
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) n]

/-- A local absolute rounding error of δ accumulates at most linearly;
the normalized recurrence is contractive. -/
theorem normalizedCoefficient_approx_bound {β r δ : ℝ} (hβ : 0 < β)
    (hr : 0 ≤ r) (a : ℕ → ℝ) (ha0 : a 0 = 1)
    (hstep : ∀ n : ℕ, |a (n + 1) -
      (β - (r + 2 * n)) / (r + 2 * n + β + 2) * a n| ≤ δ) (n : ℕ) :
    |normalizedCoefficient β r n - a n| ≤ n * δ := by
  induction n with
  | zero => simp [normalizedCoefficient, ha0]
  | succ n ih =>
    let t := (β - (r + 2 * n)) / (r + 2 * n + β + 2)
    have ht : |t| ≤ 1 := recurrence_factor_abs_le_one hβ hr n
    have hs : |t * a n - a (n + 1)| ≤ δ := by
      simpa only [abs_sub_comm, t] using hstep n
    calc
      |normalizedCoefficient β r (n + 1) - a (n + 1)| =
          |t * (normalizedCoefficient β r n - a n) + (t * a n - a (n + 1))| := by
        rw [normalizedCoefficient]
        congr 1
        dsimp [t]
        ring
      _ ≤ |t * (normalizedCoefficient β r n - a n)| + |t * a n - a (n + 1)| := abs_add_le _ _
      _ ≤ |normalizedCoefficient β r n - a n| + δ := by
        rw [abs_mul]
        nlinarith [abs_nonneg (normalizedCoefficient β r n - a n)]
      _ ≤ ((n + 1 : ℕ) : ℝ) * δ := by push_cast; nlinarith

/-- Integer division gives a one-unit outward error before scaling. -/
lemma int_quotient_rounding_error (p : ℤ) {q : ℤ} (hq : 0 < q) :
    |(p : ℝ) / q - (p / q : ℤ)| ≤ 1 := by
  have hrem0 := Int.emod_nonneg p (ne_of_gt hq)
  have hrem1 := Int.emod_lt_of_pos p hq
  have hid := Int.ediv_mul_add_emod p q
  have hid' : (q : ℝ) * (p / q : ℤ) + (p % q : ℤ) = p := by
    exact_mod_cast (by simpa only [mul_comm] using hid : q * (p / q) + p % q = p)
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hr0 : (0 : ℝ) ≤ (p % q : ℤ) := by exact_mod_cast hrem0
  have hr1 : ((p % q : ℤ) : ℝ) < q := by exact_mod_cast hrem1
  have heq : (p : ℝ) / q - (p / q : ℤ) = (p % q : ℤ) / (q : ℝ) := by
    apply (eq_div_iff (ne_of_gt hq')).mpr
    field_simp
    nlinarith
  rw [heq, abs_of_nonneg (div_nonneg hr0 hq'.le)]
  exact (div_lt_one hq').mpr hr1 |>.le

lemma scaled_integer_step_error (p a : ℤ) {q S : ℤ} (hq : 0 < q) (hS : 0 < S) :
    |((p * a / q : ℤ) : ℝ) / S - (p : ℝ) / q * ((a : ℝ) / S)| ≤ 1 / S := by
  have hh := int_quotient_rounding_error (p * a) hq
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have heq : ((p * a / q : ℤ) : ℝ) / S - (p : ℝ) / q * ((a : ℝ) / S) =
      -(((p * a : ℤ) : ℝ) / q - (p * a / q : ℤ)) / S := by
    push_cast
    ring
  rw [heq, abs_div, abs_neg, abs_of_pos hS']
  exact div_le_div_of_nonneg_right hh hS'.le

def roundedCoefficient (B D r S : ℤ) : ℕ → ℤ
  | 0 => S
  | n + 1 => (B - D * (r + 2 * n)) * roundedCoefficient B D r S n /
      (B + D * (r + 2 * n + 2))

/-- The integer recurrence approximates the analytic normalized coefficients
with an explicit error independent of the size of the intermediate integers. -/
theorem roundedCoefficient_error {B D r S : ℤ} (hB : 0 < B) (hD : 0 < D)
    (hr : 0 ≤ r) (hS : 0 < S) (n : ℕ) :
    |normalizedCoefficient ((B : ℝ) / D) r n - (roundedCoefficient B D r S n : ℝ) / S| ≤
      n * (1 / (S : ℝ)) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  apply normalizedCoefficient_approx_bound (by positivity) (by exact_mod_cast hr)
    (fun n => (roundedCoefficient B D r S n : ℝ) / S)
    (by simp [roundedCoefficient, ne_of_gt hS'])
  intro k
  have hq : 0 < B + D * (r + 2 * (k : ℤ) + 2) := by positivity
  have hh := scaled_integer_step_error (B - D * (r + 2 * (k : ℤ)))
    (roundedCoefficient B D r S k) hq hS
  have hratio : ((B - D * (r + 2 * (k : ℤ)) : ℤ) : ℝ) /
      ((B + D * (r + 2 * (k : ℤ) + 2) : ℤ) : ℝ) =
      ((B : ℝ) / D - (r + 2 * k)) / (r + 2 * k + (B : ℝ) / D + 2) := by
    push_cast
    field_simp
    ring
  simpa only [roundedCoefficient, hratio] using hh

end KsIndex.PowerArc
