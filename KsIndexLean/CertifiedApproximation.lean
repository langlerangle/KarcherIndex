module

public import Mathlib

@[expose] public section


/-! Elementary error bounds for finite numerical quadratic-form certificates. -/

namespace KsIndex.CertifiedApproximation

lemma product_error {x y a b e f : ℝ} (he : 0 ≤ e)
    (hx : |x - a| ≤ e) (hy : |y - b| ≤ f) :
    |x * y - a * b| ≤ |a| * f + |b| * e + e * f := by
  have hxy : x * y - a * b = a * (y - b) + b * (x - a) + (x - a) * (y - b) := by ring
  rw [hxy]
  calc
    _ ≤ |a * (y - b)| + |b * (x - a)| + |(x - a) * (y - b)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ |a| * f + |b| * e + e * f := by
      simp only [abs_mul]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hx (abs_nonneg _)))
        (mul_le_mul hx hy (abs_nonneg _) he)

lemma square_error {x a e : ℝ} (he : 0 ≤ e) (hx : |x - a| ≤ e) :
    |x ^ 2 - a ^ 2| ≤ e * (2 * |a| + e) := by
  have hh := product_error he hx hx
  rw [← sq, ← sq] at hh
  nlinarith

lemma finite_linear_error {ι : Type*} (s : Finset ι) (w x a e : ι → ℝ)
    (hx : ∀ i ∈ s, |x i - a i| ≤ e i) :
    |(∑ i ∈ s, w i * x i) - ∑ i ∈ s, w i * a i| ≤ ∑ i ∈ s, |w i| * e i := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ s, |w i * x i - w i * a i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, |w i| * e i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (hx i hi) (abs_nonneg _)

/-- The weights may have either sign; the error budget uses their absolute values. -/
theorem finite_quadratic_error {ι : Type*} (s : Finset ι) (w x a e : ι → ℝ)
    (he : ∀ i ∈ s, 0 ≤ e i) (hx : ∀ i ∈ s, |x i - a i| ≤ e i) :
    |(∑ i ∈ s, w i * x i ^ 2) - ∑ i ∈ s, w i * a i ^ 2| ≤
      ∑ i ∈ s, |w i| * (e i * (2 * |a i| + e i)) :=
  finite_linear_error s w (fun i => x i ^ 2) (fun i => a i ^ 2)
    (fun i => e i * (2 * |a i| + e i))
    (fun i hi => square_error (he i hi) (hx i hi))

end KsIndex.CertifiedApproximation
