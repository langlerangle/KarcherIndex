module

public import KsIndexLean.AlphaTrialGroupsReflected
public import KsIndexLean.AlphaTrialGroupReduction

@[expose] public section


/-! Finite group reduction for reflected trial shifts. -/
noncomputable section
namespace KsIndex.OppositeHalf
open CircleQ PowerArc KsIndex.AlphaRemarkTrial

theorem trial_group_reduction_refl (s : Finset (Fin 25)) (β r_g z : ℝ)
    (hβ : 0 < β) (hz : 0 < z)
    (hexp : ∀ i ∈ s, exponent i = β) (hbase : ∀ i ∈ s, baseR i = r_g)
    (hd : ∀ i ∈ s, ∀ u : ℕ, u < chainLenR i → z + u + 1 - (r_g - β) / 2 ≠ 0) :
    (∑ i ∈ s, (coefficient i).re * powerArcStieltjes β (9 + shift i) z) =
      (∑ i ∈ s, (coefficient i).re * (-1 : ℝ) ^ chainLenR i *
          zChainCoeff β r_g z (chainLenR i)) * powerArcStieltjes β r_g z
      + ∑ i ∈ s, (coefficient i).re *
          ((∑ u ∈ Finset.range (chainLenR i),
              (-1 : ℝ) ^ u * g β ((9 + (shift i : ℝ)) + 2 * u) / (z + u))
            + (-1 : ℝ) ^ chainLenR i * zChainForce β r_g z (chainLenR i)) := by
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hri : β ≤ 9 + (shift i : ℝ) := by
    rw [← hexp i hi]
    exact exponent_le_baseterm_refl i
  have hterm := paS_iter hβ hri hz (chainLenR i)
  have hrel : (9 + (shift i : ℝ)) + 2 * (chainLenR i : ℝ) = r_g := by
    rw [← hbase i hi]
    exact chainLenR_rel i
  rw [hrel] at hterm
  have hrg : β ≤ r_g := by
    rw [← hrel]
    have := Nat.cast_nonneg (α := ℝ) (chainLenR i)
    linarith
  have hchain := paS_z_chain hβ hrg hz (chainLenR i) (hd i hi)
  rw [hterm, hchain]
  ring

end KsIndex.OppositeHalf
