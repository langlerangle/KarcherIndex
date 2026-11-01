module

public import KsIndexLean.AlphaGroupMultiplierBridge
public import KsIndexLean.AlphaTrialReducedReflected

@[expose] public section


/-! Reflected transform multipliers in normalized lattice coordinates. -/
noncomputable section
namespace KsIndex.OppositeHalf
open CircleQ PowerArc KsIndex.AlphaRemarkTrial

/-- The two chain signs cancel; the group's multiplier is a finite lattice sum. -/
theorem trialGroupMultR_eq_normalized (s : Finset (Fin 25)) (β r z : ℝ) :
    trialGroupMultR s β r z =
      ∑ i ∈ s, (coefficient i).re * normalizedCoefficient β (2*z-r) (chainLenR i) := by
  unfold trialGroupMultR
  apply Finset.sum_congr rfl
  intro i _
  rw [zChainCoeff_eq_normalized]
  have hs : (-1 : ℝ)^(chainLenR i) * (-1 : ℝ)^(chainLenR i) = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = (coefficient i).re * ((-1 : ℝ)^(chainLenR i) * (-1 : ℝ)^(chainLenR i)) *
        normalizedCoefficient β (2*z-r) (chainLenR i) := by ring
    _ = _ := by rw [hs]; ring

end KsIndex.OppositeHalf
