module

public import KsIndexLean.AlphaGroupSeedRest

@[expose] public section


/-! Shared-seed error propagation through the finite group remainder. -/
noncomputable section
namespace KsIndex.OppositeHalf
open PowerArc

/-- The whole group remainder is affine in its common odd seed. -/
theorem seededGroupRest_affine (p : Finset (Fin 25)) (β : ℝ) (r : ℤ) (z seed : ℝ)
    (c : Fin 25 → ℝ) (d : Fin 25 → ℤ) (k : Fin 25 → ℕ) :
    seededGroupRest p β r z seed c d k = seededGroupRest p β r z 0 c d k +
      seed*(seededGroupRest p β r z 1 c d k-seededGroupRest p β r z 0 c d k) := by
  unfold seededGroupRest
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hp : (∑ u ∈ Finset.range (k i),
      (-1 : ℝ)^u*integerSeedValue β seed (d i+2*(u : ℤ))/(z+u)) =
      (∑ u ∈ Finset.range (k i),
        (-1 : ℝ)^u*integerSeedValue β 0 (d i+2*(u : ℤ))/(z+u)) +
      seed*((∑ u ∈ Finset.range (k i),
        (-1 : ℝ)^u*integerSeedValue β 1 (d i+2*(u : ℤ))/(z+u)) -
        (∑ u ∈ Finset.range (k i),
          (-1 : ℝ)^u*integerSeedValue β 0 (d i+2*(u : ℤ))/(z+u))) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    rw [integerSeedValue_affine β seed]
    ring
  rw [hp, integerSeedValue_affine β seed r]
  ring

/-- Exact error identity, retaining cancellation across the entire group. -/
theorem seededGroupRest_error (p : Finset (Fin 25)) (β : ℝ) (r : ℤ) (z a b : ℝ)
    (c : Fin 25 → ℝ) (d : Fin 25 → ℤ) (k : Fin 25 → ℕ) :
    |seededGroupRest p β r z a c d k-seededGroupRest p β r z b c d k| =
      |a-b| * |seededGroupRest p β r z 1 c d k-seededGroupRest p β r z 0 c d k| := by
  rw [seededGroupRest_affine p β r z a, seededGroupRest_affine p β r z b,
    ← abs_mul]
  congr 1
  ring

/-- Certified seed-radius and slope bounds imply a remainder error bound. -/
theorem seededGroupRest_error_le (p : Finset (Fin 25)) (β : ℝ) (r : ℤ) (z a b ε B : ℝ)
    (c : Fin 25 → ℝ) (d : Fin 25 → ℤ) (k : Fin 25 → ℕ)
    (hseed : |a-b| ≤ ε)
    (hslope : |seededGroupRest p β r z 1 c d k-seededGroupRest p β r z 0 c d k| ≤ B) :
    |seededGroupRest p β r z a c d k-seededGroupRest p β r z b c d k| ≤ ε*B := by
  rw [seededGroupRest_error]
  exact mul_le_mul hseed hslope (abs_nonneg _) (le_trans (abs_nonneg _) hseed)

end KsIndex.OppositeHalf
