module

public import KsIndexLean.AlphaTrialReduced
public import KsIndexLean.PowerArcNormalized

@[expose] public section


/-! Identification of the transform-chain multiplier with the lattice multiplier. -/
noncomputable section
namespace KsIndex.OppositeHalf
open CircleQ PowerArc KsIndex.AlphaRemarkTrial

theorem zChainCoeff_eq_normalized (β r z : ℝ) (k : ℕ) :
    zChainCoeff β r z k = (-1 : ℝ)^k * normalizedCoefficient β (2*z-r) k := by
  induction k with
  | zero => simp [zChainCoeff, normalizedCoefficient]
  | succ k ih =>
    rw [zChainCoeff, normalizedCoefficient, ih, pow_succ]
    have he : (z+k+1-(r+β+2)/2)/(z+k+1-(r-β)/2) =
        -((β-((2*z-r)+2*k))/((2*z-r)+2*k+β+2)) := by
      rw [show z+k+1-(r+β+2)/2 = -((β-((2*z-r)+2*k))/2) by ring,
        show z+k+1-(r-β)/2 = ((2*z-r)+2*k+β+2)/2 by ring]
      simp only [neg_div, div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [he]
    ring

/-- The two chain signs cancel; the group's multiplier is a finite lattice sum. -/
theorem trialGroupMult_eq_normalized (s : Finset (Fin 25)) (β r z : ℝ) :
    trialGroupMult s β r z =
      ∑ i ∈ s, (coefficient i).re * normalizedCoefficient β (2*z-r) (chainLen i) := by
  unfold trialGroupMult
  apply Finset.sum_congr rfl
  intro i _
  rw [zChainCoeff_eq_normalized]
  have hs : (-1 : ℝ)^(chainLen i) * (-1 : ℝ)^(chainLen i) = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = (coefficient i).re * ((-1 : ℝ)^(chainLen i) * (-1 : ℝ)^(chainLen i)) *
        normalizedCoefficient β (2*z-r) (chainLen i) := by ring
    _ = _ := by rw [hs]; ring

end KsIndex.OppositeHalf
