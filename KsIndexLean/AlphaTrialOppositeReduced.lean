module

public import KsIndexLean.AlphaTrialMomentReduced
public import KsIndexLean.AlphaReflectedMass

@[expose] public section


/-! The positive-index opposite-half contribution in reduced transform coordinates. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ PowerArc OppositeHalf

/-- Four central reflected terms of a shifted moment. -/
def reflectedMomentPrefix (z : ℝ) : ℝ :=
  ∑ t ∈ Finset.range 4, reflectedDemod t / ((t : ℝ) + z)

/-- Reduced expression for the opposite-half contribution at a positive residual index. -/
def reducedOpposite (n : ℤ) : ℝ :=
  2 / Real.pi * (-1 : ℝ)^n *
    (3 * reflectedMass
      - sigP n * (1/2) *
        (reflectedMomentPrefix ((n : ℝ)+1/2) + reducedMomentLower ((n : ℝ)+9/2))
      - 12 / (6*(n : ℝ)+1) * (1/6) *
        (reflectedMomentPrefix (1/3) + reducedMomentLower (13/3)))

theorem oppositeResidualSum_eq_reduced (n : ℤ) (hn : 1 ≤ n) :
    oppositeResidualSum n = reducedOpposite n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hred := stieltjes_side_reduced ((n : ℝ)+9/2) (by linarith)
    (fun i u _ => denom_nFamily i n u)
  change (∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
      powerArcStieltjes (exponent i) (9-shift i) ((n : ℝ)+9/2)) =
      reducedMomentLower ((n : ℝ)+9/2) at hred
  have h := opposite_half_group_decomposition n hn
  change oppositeResidualSum n = _ at h
  rw [show ((n : ℝ)+1/2)+4 = (n : ℝ)+9/2 by ring,
    show (1/3 : ℝ)+4 = 13/3 by norm_num, hred, reducedMomentLower_eq, reflectedDemod_tsum_eq] at h
  exact h

/-- The actual residual with both its opposite-half sum and signed moment reduced. -/
theorem realResidual_eq_reduced (s : ℝ) (n : ℤ) (hn : 1 ≤ n) :
    realResidual s n =
      (1+s^2) * sigP n * (trial n).re + 2*s^2 * reducedOpposite n +
      (24*s^2 / (Real.pi * |6*(n : ℝ)+1|)) * (-1 : ℝ)^n *
        (trialMomentPrefix + (reducedMomentUpper (14/3) + reducedMomentLower (13/3))/6) := by
  rw [realResidual_split, oppositeResidualSum_eq_reduced n hn,
    signedTrialMoment_eq_reduced]

end KsIndex.AlphaRemarkTrial
