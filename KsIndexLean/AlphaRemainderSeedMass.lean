module

public import KsIndexLean.AlphaReflectedMass
public import KsIndexLean.AlphaPositiveMass
public import KsIndexLean.PowerArcIntegerSeed

@[expose] public section


/-! # Mass endpoint sums in shared-seed form

The finite endpoint sums in `reflectedMass` and `positiveMass` use normalized
power-arc coefficients at integer arguments. `normalized_g_integer_seed` rewrites
each coefficient using the odd seed `g β 1 / g β 0` for its exponent family.
The same rewriting applies to the finite demodulated prefixes. These identities
supply the shared-seed expressions used by the interval bounds. -/
noncomputable section
namespace KsIndex.OppositeHalf
open CircleQ PowerArc KsIndex.AlphaRemarkTrial

private lemma g_exponent_zero_ne (i : Fin 25) : g (exponent i) 0 ≠ 0 :=
  (g_pos_of_mem_unit (exponent_pos i) le_rfl zero_le_one).ne'

/-- Reflected-mass endpoint sum, each g-endpoint rewritten on the shared odd seed. -/
theorem reflectedMass_endpoint_seed :
    (∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
        (((9 - shift i) + exponent i) * g (exponent i) (9 - shift i) / (2 * exponent i)))
      = ∑ i : Fin 25, (coefficient i).re * (((9 - shift i) + exponent i) / (2 * exponent i)) *
          integerSeedValue (exponent i) (g (exponent i) 1 / g (exponent i) 0) (9 - shift i) := by
  apply Finset.sum_congr rfl
  intro i _
  have hseed := normalized_g_integer_seed (exponent_pos i) (9 - shift i)
  have harg : ((9 - shift i : ℤ) : ℝ) = 9 - (shift i : ℝ) := by push_cast; ring
  rw [harg] at hseed
  rw [← hseed]; ring

/-- Positive-mass endpoint sum, each g-endpoint rewritten on the shared odd seed. -/
theorem positiveMass_endpoint_seed :
    (∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
        (((9 + shift i) + exponent i) * g (exponent i) (9 + shift i) / (2 * exponent i)))
      = ∑ i : Fin 25, (coefficient i).re * (((9 + shift i) + exponent i) / (2 * exponent i)) *
          integerSeedValue (exponent i) (g (exponent i) 1 / g (exponent i) 0) (9 + shift i) := by
  apply Finset.sum_congr rfl
  intro i _
  have hseed := normalized_g_integer_seed (exponent_pos i) (9 + shift i)
  have harg : ((9 + shift i : ℤ) : ℝ) = 9 + (shift i : ℝ) := by push_cast; ring
  rw [harg] at hseed
  rw [← hseed]; ring

/-! ### Finite demod prefixes on the shared seed -/

/-- Reflected demod term with each g-endpoint on the shared odd seed. -/
theorem reflectedDemod_seed (t : ℕ) :
    reflectedDemod t = (-1 : ℝ) ^ t * ∑ i : Fin 25, (coefficient i).re *
      integerSeedValue (exponent i) (g (exponent i) 1 / g (exponent i) 0)
        (2 * (t : ℤ) + 1 - shift i) := by
  rw [reflectedDemod_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hseed := normalized_g_integer_seed (exponent_pos i) (2 * (t : ℤ) + 1 - shift i)
  have harg : ((2 * (t : ℤ) + 1 - shift i : ℤ) : ℝ) = (2 * (t : ℝ) + 1) - (shift i : ℝ) := by
    push_cast; ring
  rw [harg] at hseed
  rw [hseed]

/-- Positive demod term with each g-endpoint on the shared odd seed. -/
theorem positiveDemod_seed (t : ℕ) :
    positiveDemod t = (-1 : ℝ) ^ t * ∑ i : Fin 25, (coefficient i).re *
      integerSeedValue (exponent i) (g (exponent i) 1 / g (exponent i) 0)
        (2 * (t : ℤ) + 1 + shift i) := by
  rw [positiveDemod_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hseed := normalized_g_integer_seed (exponent_pos i) (2 * (t : ℤ) + 1 + shift i)
  have harg : ((2 * (t : ℤ) + 1 + shift i : ℤ) : ℝ) = (2 * (t : ℝ) + 1) + (shift i : ℝ) := by
    push_cast; ring
  rw [harg] at hseed
  rw [hseed]

end KsIndex.OppositeHalf

#print axioms KsIndex.OppositeHalf.reflectedMass_endpoint_seed
#print axioms KsIndex.OppositeHalf.positiveMass_endpoint_seed
#print axioms KsIndex.OppositeHalf.reflectedDemod_seed
#print axioms KsIndex.OppositeHalf.positiveDemod_seed
