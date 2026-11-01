module

public import KsIndexLean.AlphaTrialMomentReduced
public import KsIndexLean.AlphaNegativeOppositeGroups
public import KsIndexLean.AlphaPositiveMass

@[expose] public section


/-! The negative-index residual in reduced transform coordinates. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ PowerArc OppositeHalf

def positiveMomentPrefix (z : ℝ) : ℝ :=
  ∑ t ∈ Finset.range 4, positiveDemod t / ((t : ℝ)+z)

def reducedNegativeOpposite (n : ℤ) : ℝ :=
  2/Real.pi * (-1 : ℝ)^n *
    (3*positiveMass - sigP (-n)*(1/2)*
      (positiveMomentPrefix ((n : ℝ)+1/2)+reducedMomentUpper ((n : ℝ)+9/2))
      -12/(6*(n : ℝ)-1)*(1/6)*
        (positiveMomentPrefix (2/3)+reducedMomentUpper (14/3)))

theorem negativeOpposite_eq_reduced (n : ℤ) (hn : 1 ≤ n) :
    oppositeResidualSum (-n) = reducedNegativeOpposite n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hred := stieltjes_side_reduced_refl ((n : ℝ)+9/2) (by linarith)
    (fun i u _ => denom_nFamily i n u)
  change (∑ i : Fin 25, ((coefficient i).re/g (exponent i) 0)*
      powerArcStieltjes (exponent i) (9+shift i) ((n : ℝ)+9/2)) =
      reducedMomentUpper ((n : ℝ)+9/2) at hred
  have h := negative_opposite_group_decomposition n hn
  rw [show ((n : ℝ)+1/2)+4 = (n : ℝ)+9/2 by ring,
    show (2/3 : ℝ)+4 = 14/3 by norm_num, hred, reducedMomentUpper_eq,
    positiveDemod_tsum_eq] at h
  exact h

theorem realResidual_neg_eq_reduced (s : ℝ) (n : ℤ) (hn : 1 ≤ n) :
    realResidual s (-n) =
      (1+s^2)*sigP (-n)*(trial (-n)).re + 2*s^2*reducedNegativeOpposite n +
      (24*s^2/(Real.pi*|6*(-(n : ℝ))+1|)) * (-1 : ℝ)^n *
        (trialMomentPrefix+(reducedMomentUpper (14/3)+reducedMomentLower (13/3))/6) := by
  have hphase : (-1 : ℝ)^(-n) = (-1 : ℝ)^n := by
    simpa using negOne_zpow_sub 0 n
  rw [realResidual_split, negativeOpposite_eq_reduced n hn,
    signedTrialMoment_eq_reduced, hphase]
  simp only [Int.cast_neg]

end KsIndex.AlphaRemarkTrial
