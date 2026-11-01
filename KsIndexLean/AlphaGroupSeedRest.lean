module

public import KsIndexLean.AlphaGroupRationalRest
public import KsIndexLean.PowerArcIntegerSeed

@[expose] public section


/-! Shared-seed evaluation of the finite group remainders. -/
noncomputable section
namespace KsIndex.OppositeHalf
open PowerArc KsIndex.AlphaRemarkTrial

/-- The rational group remainder evaluated using one common odd seed. -/
def seededGroupRest (p : Finset (Fin 25)) (β : ℝ) (r : ℤ) (z seed : ℝ)
    (c : Fin 25 → ℝ) (d : Fin 25 → ℤ) (k : Fin 25 → ℕ) : ℝ :=
  ∑ i ∈ p, c i *
    ((∑ u ∈ Finset.range (k i),
      (-1 : ℝ)^u * integerSeedValue β seed (d i+2*(u : ℤ))/(z+u)) +
      (-1 : ℝ)^(k i)*integerSeedValue β seed r*zChainForceUnit β r z (k i))

/-- Exact substitution of analytic endpoints by their shared-seed recurrence. -/
theorem rationalGroupRest_eq_seeded (p : Finset (Fin 25)) {β : ℝ} (hβ : 0 < β)
    (r : ℤ) (z : ℝ) (c : Fin 25 → ℝ) (d : Fin 25 → ℤ) (k : Fin 25 → ℕ) :
    rationalGroupRest p β r z c (fun i => (d i : ℝ)) k (fun t => g β t/g β 0) =
      seededGroupRest p β r z (g β 1/g β 0) c d k := by
  unfold rationalGroupRest seededGroupRest
  apply Finset.sum_congr rfl
  intro i hi
  simp only
  rw [normalized_g_integer_seed hβ r]
  congr 2
  apply Finset.sum_congr rfl
  intro u hu
  have he : (d i : ℝ)+2*(u : ℝ) = ((d i+2*(u : ℤ) : ℤ) : ℝ) := by push_cast; ring
  rw [he, normalized_g_integer_seed hβ]

/-- Forward group remainder with the actual common seed. -/
theorem trialGroupRest_eq_seeded (p : Finset (Fin 25)) {β : ℝ} (hβ : 0 < β)
    (r : ℤ) (z : ℝ) :
    trialGroupRest p β r z/g β 0 = seededGroupRest p β r z (g β 1/g β 0)
      (fun i => (coefficient i).re) (fun i => 9-shift i) chainLen := by
  rw [trialGroupRest_normalized]
  simpa only [Int.cast_sub, Int.cast_ofNat] using
    rationalGroupRest_eq_seeded p hβ r z (fun i => (coefficient i).re)
      (fun i => 9-shift i) chainLen

/-- Reflected group remainder with the same actual common seed. -/
theorem trialGroupRestR_eq_seeded (p : Finset (Fin 25)) {β : ℝ} (hβ : 0 < β)
    (r : ℤ) (z : ℝ) :
    trialGroupRestR p β r z/g β 0 = seededGroupRest p β r z (g β 1/g β 0)
      (fun i => (coefficient i).re) (fun i => 9+shift i) chainLenR := by
  rw [trialGroupRestR_normalized]
  simpa only [Int.cast_add, Int.cast_ofNat] using
    rationalGroupRest_eq_seeded p hβ r z (fun i => (coefficient i).re)
      (fun i => 9+shift i) chainLenR

end KsIndex.OppositeHalf
