module

public import KsIndexLean.CertifiedApproximation

@[expose] public section


/-! Interval propagation for finite bilinear sums with signed coefficients. -/
namespace KsIndex.CertifiedApproximation

theorem finite_bilinear_error {ι : Type*} [Fintype ι]
    (C : ι → ι → ℝ) (x a e : ι → ℝ)
    (he : ∀ i, 0 ≤ e i) (hx : ∀ i, |x i-a i| ≤ e i) :
    |(∑ i, ∑ j, C i j*(x i*x j))-(∑ i, ∑ j, C i j*(a i*a j))| ≤
      ∑ i, ∑ j, |C i j| *(|a i| *e j+|a j| *e i+e i*e j) := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  exact finite_linear_error Finset.univ (C i) (fun j => x i*x j)
    (fun j => a i*a j) (fun j => |a i| *e j+|a j| *e i+e i*e j)
    (fun j _ => product_error (he i) (hx i) (hx j))

lemma abs_le_center_radius {x a e : ℝ} (hx : |x-a| ≤ e) : |x| ≤ |a|+e := by
  have h := abs_add_le a (x-a)
  rw [add_sub_cancel] at h
  linarith

end KsIndex.CertifiedApproximation
