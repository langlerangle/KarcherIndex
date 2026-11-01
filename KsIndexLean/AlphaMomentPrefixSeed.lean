module

public import KsIndexLean.AlphaTrialMomentTransforms
public import KsIndexLean.PowerArcIntegerSeed

@[expose] public section


/-! Integer-seed representation of the eight central modes in the signed moment. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ PowerArc OppositeHalf

def seededTrialValue (m : ℤ) : ℝ :=
  ∑ i : Fin 25, (coefficient i).re *
    integerSeedValue (exponent i) (g (exponent i) 1/g (exponent i) 0)
      (2*m+shift i+1)

theorem vTrial_eq_seeded (m : ℤ) : vTrial m = seededTrialValue m := by
  rw [vTrial_eq_sum]
  unfold seededTrialValue
  apply Finset.sum_congr rfl
  intro i _
  have hc : 2*(m : ℝ)+((shift i : ℝ)+1) = ((2*m+shift i+1 : ℤ) : ℝ) := by
    push_cast
    ring
  rw [hc, normalized_g_integer_seed (exponent_pos i)]

def seededMomentPrefix : ℝ :=
  ∑ k ∈ Finset.range 4, (-1 : ℝ)^(k : ℤ) * seededTrialValue (k : ℤ) /
    (6*(k : ℝ)+4) +
  ∑ k ∈ Finset.range 4, (-1 : ℝ)^(-((k : ℤ)+1)) * seededTrialValue (-((k : ℤ)+1)) /
    (6*((-((k : ℤ)+1):ℤ):ℝ)+4)

theorem trialMomentPrefix_eq_seeded : trialMomentPrefix = seededMomentPrefix := by
  unfold trialMomentPrefix seededMomentPrefix
  change (∑ k ∈ Finset.range 4, (-1 : ℝ)^(k : ℤ) * vTrial (k : ℤ) /
    (6*(k : ℝ)+4)) +
    (∑ k ∈ Finset.range 4, (-1 : ℝ)^(-((k : ℤ)+1)) * vTrial (-((k : ℤ)+1)) /
    (6*((-((k : ℤ)+1):ℤ):ℝ)+4)) = _
  simp only [vTrial_eq_seeded]

end KsIndex.AlphaRemarkTrial
#print axioms KsIndex.AlphaRemarkTrial.trialMomentPrefix_eq_seeded
