module

public import KsIndexLean.PowerArcRounding

@[expose] public section


/-! Error bounds for finite rounded Stieltjes sums. -/

namespace KsIndex.PowerArc

/-- A linearly accumulated coefficient error and a separate per-term rounding
error give a finite Stieltjes sum enclosure. -/
theorem finite_stieltjes_approx_bound (f a b : ℕ → ℝ) (N : ℕ) (z δ η : ℝ)
    (hz : 0 < z) (hδ : 0 ≤ δ)
    (hfa : ∀ k < N, |f k - a k| ≤ k * δ)
    (hab : ∀ k < N, |(-1 : ℝ) ^ k * a k / ((k : ℝ) + z) - b k| ≤ η) :
    |(∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * f k / ((k : ℝ) + z)) -
        ∑ k ∈ Finset.range N, b k| ≤ N * ((N : ℝ) * δ / z + η) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.range N,
        |(-1 : ℝ) ^ k * f k / ((k : ℝ) + z) - b k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range N, ((N : ℝ) * δ / z + η) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkN : k < N := Finset.mem_range.mp hk
      have hkR : (k : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt hkN)
      have hkz : 0 < (k : ℝ) + z := by positivity
      have herr : |(-1 : ℝ) ^ k * (f k - a k) / ((k : ℝ) + z)| ≤ (N : ℝ) * δ / z := by
        rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_pos hkz]
        calc
          _ ≤ ((k : ℝ) * δ) / ((k : ℝ) + z) :=
            div_le_div_of_nonneg_right (hfa k hkN) hkz.le
          _ ≤ ((N : ℝ) * δ) / ((k : ℝ) + z) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hkR hδ) hkz.le
          _ ≤ ((N : ℝ) * δ) / z :=
            div_le_div_of_nonneg_left (by positivity) hz (by linarith [Nat.cast_nonneg (α := ℝ) k])
      have hid : (-1 : ℝ) ^ k * f k / ((k : ℝ) + z) - b k =
          (-1 : ℝ) ^ k * (f k - a k) / ((k : ℝ) + z) +
            ((-1 : ℝ) ^ k * a k / ((k : ℝ) + z) - b k) := by ring
      rw [hid]
      exact (abs_add_le _ _).trans (add_le_add herr (hab k hkN))
    _ = _ := by simp; ring

/-- Integer evaluation of a single weighted coefficient. -/
def roundedStieltjesTerm (t : ℕ → ℤ) (Znum Zden : ℤ) (k : ℕ) : ℤ :=
  (((-1 : ℤ) ^ k * Zden) * t k) / ((k : ℤ) * Zden + Znum)

theorem roundedStieltjesTerm_error (t : ℕ → ℤ) (Znum Zden S : ℤ)
    (hnum : 0 < Znum) (hden : 0 < Zden) (hS : 0 < S) (k : ℕ) :
    |(-1 : ℝ) ^ k * ((t k : ℝ) / S) / ((k : ℝ) + (Znum : ℝ) / Zden) -
      (roundedStieltjesTerm t Znum Zden k : ℝ) / S| ≤ 1 / S := by
  have hq : 0 < (k : ℤ) * Zden + Znum := by positivity
  have hdenR : (0 : ℝ) < Zden := by exact_mod_cast hden
  have hratio : (((-1 : ℤ) ^ k * Zden : ℤ) : ℝ) /
      (((k : ℤ) * Zden + Znum : ℤ) : ℝ) =
      (-1 : ℝ) ^ k / ((k : ℝ) + (Znum : ℝ) / Zden) := by
    push_cast
    field_simp
  have hh := scaled_integer_step_error ((-1 : ℤ) ^ k * Zden) (t k) hq hS
  rw [hratio, abs_sub_comm] at hh
  convert hh using 1
  dsimp [roundedStieltjesTerm]
  congr 1
  ring

/-- A rounded recurrence table and rounded weighted terms enclose the finite
normalized Stieltjes sum, with an explicit elementary error. -/
theorem roundedStieltjesSum_error (B D r S Znum Zden : ℤ) (N : ℕ)
    (hB : 0 < B) (hD : 0 < D) (hr : 0 ≤ r) (hS : 0 < S)
    (hnum : 0 < Znum) (hden : 0 < Zden) :
    |(∑ k ∈ Finset.range N, (-1 : ℝ) ^ k *
        normalizedCoefficient ((B : ℝ) / D) r k / ((k : ℝ) + (Znum : ℝ) / Zden)) -
      ∑ k ∈ Finset.range N,
        (roundedStieltjesTerm (roundedCoefficient B D r S) Znum Zden k : ℝ) / S| ≤
      N * ((N : ℝ) * (1 / (S : ℝ)) / ((Znum : ℝ) / Zden) + 1 / (S : ℝ)) := by
  have hSR : (0 : ℝ) < S := by exact_mod_cast hS
  have hnumR : (0 : ℝ) < Znum := by exact_mod_cast hnum
  have hdenR : (0 : ℝ) < Zden := by exact_mod_cast hden
  apply finite_stieltjes_approx_bound _
    (fun k => (roundedCoefficient B D r S k : ℝ) / S) _ N
    ((Znum : ℝ) / Zden) (1 / (S : ℝ)) (1 / (S : ℝ)) (by positivity) (by positivity)
  · intro k _
    exact roundedCoefficient_error hB hD hr hS k
  · intro k _
    exact roundedStieltjesTerm_error _ Znum Zden S hnum hden hS k

end KsIndex.PowerArc
