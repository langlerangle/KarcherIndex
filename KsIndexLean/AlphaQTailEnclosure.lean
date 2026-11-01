module

public import KsIndexLean.AlphaTrialProductTailEnergy
public import KsIndexLean.FiniteBilinearEnclosure

@[expose] public section


/-! Finite interval certificates for the concrete trial's energy tails. -/
namespace KsIndex.AlphaRemarkTrial
open PowerArc CertifiedApproximation

noncomputable def tailMatrix (r : Fin 25 → ℝ) (i j : Fin 25) : ℝ :=
  3*(coefficient i).re*(coefficient j).re*(r i+exponent i)*(r j+exponent j)/
    (2*(exponent i+exponent j))
noncomputable def tailCenter (r v : Fin 25 → ℝ) : ℝ :=
  ∑ i, ∑ j, tailMatrix r i j*(v i*v j)
noncomputable def tailRadius (r v e : Fin 25 → ℝ) : ℝ :=
  ∑ i, ∑ j, |tailMatrix r i j| * (|v i| * e j+|v j| * e i+e i*e j)
noncomputable def tailProductUpper (r v e : Fin 25 → ℝ) (c : ℝ) : ℝ :=
  ∑ i, ∑ j, |(coefficient i).re*(coefficient j).re| *
    (|c-3*(exponent j*r i+exponent i*r j)/(exponent i+exponent j)| *
      (((r i+exponent i)^2*(|v i|+e i)^2/(4*exponent i*r i)+
        (r j+exponent j)^2*(|v j|+e j)^2/(4*exponent j*r j))/2))

theorem tail_leading_interval (r v e : Fin 25 → ℝ)
    (he : ∀ i, 0 ≤ e i)
    (hv : ∀ i, |g (exponent i) (r i)/g (exponent i) 0-v i| ≤ e i) :
    |tailLeading r-tailCenter r v| ≤ tailRadius r v e := by
  have h := finite_bilinear_error (tailMatrix r)
    (fun i => g (exponent i) (r i)/g (exponent i) 0) v e he hv
  have hid : tailLeading r = ∑ i, ∑ j, tailMatrix r i j*
      ((g (exponent i) (r i)/g (exponent i) 0)*(g (exponent j) (r j)/g (exponent j) 0)) := by
    rw [tailLeading_eq]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [tailMatrix]
    ring
  rw [hid]
  exact h

theorem tail_product_interval (r v e : Fin 25 → ℝ) (c : ℝ)
    (hr : ∀ i, 1 ≤ r i) (he : ∀ i, 0 ≤ e i)
    (hv : ∀ i, |g (exponent i) (r i)/g (exponent i) 0-v i| ≤ e i) :
    tailProductError r c ≤ tailProductUpper r v e c := by
  have hsq (i : Fin 25) : (g (exponent i) (r i)/g (exponent i) 0)^2 ≤ (|v i|+e i)^2 := by
    have ha := abs_le_center_radius (hv i)
    nlinarith [sq_abs (g (exponent i) (r i)/g (exponent i) 0), abs_nonneg (v i), he i,
      abs_nonneg (g (exponent i) (r i)/g (exponent i) 0)]
  unfold tailProductError tailProductUpper
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply add_le_add
  · rw [mul_pow]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hsq i) (sq_nonneg _))
      (by have := exponent_pos i; have := hr i; positivity)
  · rw [mul_pow]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hsq j) (sq_nonneg _))
      (by have := exponent_pos j; have := hr j; positivity)

theorem trial_tail_interval (r v e : Fin 25 → ℝ) (c : ℝ)
    (hr : ∀ i, 1 ≤ r i) (he : ∀ i, 0 ≤ e i)
    (hv : ∀ i, |g (exponent i) (r i)/g (exponent i) 0-v i| ≤ e i) :
    |(∑' n : ℕ, (6*n+c)*(∑ i, tailScale i*g (exponent i) (r i+2*n))^2)-
      tailCenter r v| ≤ tailProductUpper r v e c+tailRadius r v e := by
  have h := abs_sub_le (∑' n : ℕ, (6*n+c)*(∑ i, tailScale i*g (exponent i) (r i+2*n))^2)
    (tailLeading r) (tailCenter r v)
  exact h.trans (add_le_add
    ((trial_product_tail_bound r c hr).trans (tail_product_interval r v e c hr he hv))
    (tail_leading_interval r v e he hv))

end KsIndex.AlphaRemarkTrial
