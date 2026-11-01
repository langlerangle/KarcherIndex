module

public import KsIndexLean.PowerArcFiniteTailEnergy

@[expose] public section


/-! Mixed tail estimates retaining the product of the external coefficients.
This avoids replacing a small cross coefficient by the squares of two
independently sized coefficients.
-/
namespace KsIndex.PowerArc

theorem coefficient_mixed_tail_bound {β γ r t c : ℝ} (a b : ℝ)
    (hβ : 0 < β) (hγ : 0 < γ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    |(∑' n : ℕ, (6*n+c) * (a*(g β (r+2*n)/g β 0)) *
        (b*(g γ (t+2*n)/g γ 0))) -
      a*b*(3*(((r+β)*(g β r/g β 0))*((t+γ)*(g γ t/g γ 0))/(2*(β+γ))))| ≤
      |a*b| * (|c-3*(γ*r+β*t)/(β+γ)| *
        ((((r+β)*(g β r/g β 0))^2/(4*β*r) +
          ((t+γ)*(g γ t/g γ 0))^2/(4*γ*t))/2)) := by
  have h := normalized_mixed_linear_tail_bound hβ hγ hr ht (c := c)
  have hs : (∑' n : ℕ, (6*n+c) * (a*(g β (r+2*n)/g β 0)) *
      (b*(g γ (t+2*n)/g γ 0))) =
      a*b*(∑' n : ℕ, (6*n+c)*(g β (r+2*n)/g β 0)*(g γ (t+2*n)/g γ 0)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    ring
  rw [hs, ← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

/-- A finite normalized family retains every signed leading cross term. -/
theorem coefficient_finite_tail_bound {ι : Type*} [Fintype ι]
    (β r a : ι → ℝ) (c : ℝ) (hβ : ∀ i, 0 < β i) (hr : ∀ i, 1 ≤ r i) :
    |(∑' n : ℕ, (6*n+c)*(∑ i, a i*(g (β i) (r i+2*n)/g (β i) 0))^2) -
      ∑ i, ∑ j, a i*a j*(3*(((r i+β i)*(g (β i) (r i)/g (β i) 0))*
        ((r j+β j)*(g (β j) (r j)/g (β j) 0))/(2*(β i+β j))))| ≤
      ∑ i, ∑ j, |a i*a j| *(|c-3*(β j*r i+β i*r j)/(β i+β j)| *
        ((((r i+β i)*(g (β i) (r i)/g (β i) 0))^2/(4*β i*r i)+
          ((r j+β j)*(g (β j) (r j)/g (β j) 0))^2/(4*β j*r j))/2)) := by
  let f := fun (i j : ι) (n : ℕ) =>
    (6*n+c)*(a i*(g (β i) (r i+2*n)/g (β i) 0))*
      (a j*(g (β j) (r j+2*n)/g (β j) 0))
  have hf (i j : ι) : Summable (f i j) := by
    have h := scaled_mixed_linear_summable (a i/g (β i) 0) (a j/g (β j) 0)
      (hβ i) (hβ j) (hr i) (hr j) (c := c)
    apply h.congr
    intro n
    dsimp [f]
    ring
  have hexpand : ∀ n : ℕ, (6*n+c)*(∑ i, a i*(g (β i) (r i+2*n)/g (β i) 0))^2 =
      ∑ i, ∑ j, f i j n := by
    intro n
    simp only [f, pow_two, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  have hsum : (∑' n : ℕ, ∑ i, ∑ j, f i j n) = ∑ i, ∑ j, ∑' n : ℕ, f i j n := by
    rw [Summable.tsum_finsetSum (fun i _ => summable_sum (fun j _ => hf i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact Summable.tsum_finsetSum (fun j _ => hf i j)
  simp_rw [hexpand]
  rw [hsum, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro j _
  exact coefficient_mixed_tail_bound (a i) (a j) (hβ i) (hβ j) (hr i) (hr j)

end KsIndex.PowerArc
