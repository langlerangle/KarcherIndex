module

public import KsIndexLean.PowerArcScaledTails

@[expose] public section


/-! Tail energy estimates for finite linear combinations of power-arc families. -/

namespace KsIndex.PowerArc

/-- Pairwise primitives control the full tail, including all cross terms. -/
theorem finite_linear_tail_energy_bound {ι : Type*} [Fintype ι]
    (β r u : ι → ℝ) (c : ℝ) (hβ : ∀ i, 0 < β i) (hr : ∀ i, 1 ≤ r i) :
    |(∑' n : ℕ, (6 * n + c) * (∑ i, u i * g (β i) (r i + 2 * n)) ^ 2) -
      ∑ i, ∑ j, 3 * (u i * u j * mixedPrimitive (β i) (β j) (r i) (r j))| ≤
      ∑ i, ∑ j, |c - 3 * (β j * r i + β i * r j) / (β i + β j)| *
        ((u i ^ 2 * (energyPrimitive (β i) (r i) / r i) +
          u j ^ 2 * (energyPrimitive (β j) (r j) / r j)) / 2) := by
  let f := fun (i j : ι) (n : ℕ) =>
    (6 * n + c) * (u i * g (β i) (r i + 2 * n)) * (u j * g (β j) (r j + 2 * n))
  have hf : ∀ i j, Summable (f i j) := fun i j =>
    scaled_mixed_linear_summable (u i) (u j) (hβ i) (hβ j) (hr i) (hr j)
  have hexpand : ∀ n : ℕ, (6 * n + c) * (∑ i, u i * g (β i) (r i + 2 * n)) ^ 2 =
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
  calc
    _ ≤ ∑ i, |∑ j, ((∑' n : ℕ, f i j n) -
        3 * (u i * u j * mixedPrimitive (β i) (β j) (r i) (r j)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro j _
      exact scaled_mixed_linear_tail_bound (u i) (u j) (hβ i) (hβ j) (hr i) (hr j)

end KsIndex.PowerArc
