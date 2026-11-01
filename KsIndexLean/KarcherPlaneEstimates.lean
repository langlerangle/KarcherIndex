module

public import KsIndexLean.KarcherRadialPositivity

@[expose] public section


/-! Scalar estimates for signed horizontal displacement relative to the
vertical symmetry planes of the Karcher immersion. -/
noncomputable section
namespace KsIndex.KarcherData

/-- The defect in the symmetric geometric-mean bound. -/
def planePowerDefect (r : ℝ) (m : ℕ) : ℝ :=
  1 - r ^ (2 * (m + 1)) - (m + 1 : ℕ) * r ^ m * (1 - r ^ 2)

lemma planePowerDefect_succ (r : ℝ) (m : ℕ) :
    planePowerDefect r (m + 1) = r * planePowerDefect r m +
      (1 - r) * (1 - r ^ (m + 1)) * (1 - r ^ (m + 2)) := by
  unfold planePowerDefect
  simp only [pow_mul, pow_add, pow_one, Nat.cast_add, Nat.cast_one]
  ring

lemma planePowerDefect_nonneg {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (m : ℕ) :
    0 ≤ planePowerDefect r m := by
  induction m with
  | zero => simp [planePowerDefect]
  | succ m ih =>
    rw [planePowerDefect_succ]
    exact add_nonneg (mul_nonneg hr ih) (mul_nonneg
      (mul_nonneg (by linarith) (sub_nonneg.mpr (pow_le_one₀ hr hr1.le)))
      (sub_nonneg.mpr (pow_le_one₀ hr hr1.le)))

lemma planePowerDefect_pos {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    {m : ℕ} (hm : 0 < m) : 0 < planePowerDefect r m := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  rw [planePowerDefect_succ]
  apply add_pos_of_nonneg_of_pos (mul_nonneg hr (planePowerDefect_nonneg hr hr1 n))
  exact mul_pos (mul_pos (by linarith)
    (sub_pos.mpr (pow_lt_one₀ hr hr1 (by omega))))
    (sub_pos.mpr (pow_lt_one₀ hr hr1 (by omega)))

/-- Strict power bound controlling the signed EW radial differential. -/
lemma plane_radial_power_bound {k : ℕ} (hk : 2 ≤ k) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) :
    (2 * k - 1 : ℕ) * (r ^ (2*k-2) - r ^ (2*k)) < 1 - r ^ (4*k-2) := by
  have h := planePowerDefect_pos hr hr1 (show 0 < 2*k-2 by omega)
  unfold planePowerDefect at h
  rw [show 2*k-2+1 = 2*k-1 by omega,
    show 2*(2*k-1) = 4*k-2 by omega] at h
  have hp : r ^ (2*k) = r ^ (2*k-2) * r ^ 2 := by
    rw [← pow_add]; congr 1; omega
  rw [hp]
  nlinarith

/-- An integer multiple cannot amplify the sine by more than its multiplier. -/
lemma abs_sin_nat_mul_le (n : ℕ) (t : ℝ) :
    |Real.sin ((n : ℝ) * t)| ≤ n * |Real.sin t| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, Real.sin_add]
    calc
      _ ≤ |Real.sin ((n : ℝ)*t) * Real.cos t| +
          |Real.cos ((n : ℝ)*t) * Real.sin t| := abs_add_le _ _
      _ ≤ |Real.sin ((n : ℝ)*t)| + |Real.sin t| := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
          (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _))
      _ ≤ (n + 1 : ℝ) * |Real.sin t| := by nlinarith

/-- The numerator of the signed radial differential is negative in the
upper parameter half-plane, for every radius strictly below one. -/
lemma plane_radial_numerator_neg {k : ℕ} (hk : 2 ≤ k) {r t : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (ht : 0 < t) (htpi : t < Real.pi) :
    (r^(2*k-2) - r^(2*k)) * Real.sin ((2*k-1 : ℕ) * t) -
      (1-r^(4*k-2)) * Real.sin t < 0 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ht htpi
  have hpow : 0 ≤ r^(2*k-2) - r^(2*k) := sub_nonneg.mpr
    (pow_le_pow_of_le_one hr hr1.le (by omega))
  have hsin := (le_abs_self (Real.sin ((2*k-1 : ℕ)*t))).trans
    (abs_sin_nat_mul_le (2*k-1) t)
  rw [abs_of_pos hs] at hsin
  have hmul := mul_le_mul_of_nonneg_left hsin hpow
  have hstrict := mul_lt_mul_of_pos_right (plane_radial_power_bound hk hr hr1) hs
  nlinarith

end KsIndex.KarcherData
