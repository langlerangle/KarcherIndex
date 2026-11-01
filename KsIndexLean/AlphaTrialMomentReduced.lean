module

public import KsIndexLean.AlphaTrialReducedReflected
public import KsIndexLean.AlphaTrialMomentTransforms

@[expose] public section


/-! The actual signed moment expressed through eight base Stieltjes transforms. -/
noncomputable section
namespace KsIndex.OppositeHalf
open CircleQ PowerArc KsIndex.AlphaRemarkTrial

def reducedMomentLower (z : ℝ) : ℝ :=
    (1 / g (4323618/10000000) 0) *
        (trialGroupMult grpAe (4323618/10000000) 15 z *
            powerArcStieltjes (4323618/10000000) 15 z
          + trialGroupRest grpAe (4323618/10000000) 15 z
          + (trialGroupMult grpAo (4323618/10000000) 14 z *
              powerArcStieltjes (4323618/10000000) 14 z
            + trialGroupRest grpAo (4323618/10000000) 14 z))
      + (1 / g (5676382/10000000) 0) *
        (trialGroupMult grpBe (5676382/10000000) 15 z *
            powerArcStieltjes (5676382/10000000) 15 z
          + trialGroupRest grpBe (5676382/10000000) 15 z
          + (trialGroupMult grpBo (5676382/10000000) 14 z *
              powerArcStieltjes (5676382/10000000) 14 z
            + trialGroupRest grpBo (5676382/10000000) 14 z))

theorem reducedMomentLower_eq :
    (∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
      powerArcStieltjes (exponent i) (9 - shift i) (13/3)) =
      reducedMomentLower (13/3) := by
  exact stieltjes_side_reduced (13/3) (by norm_num) denom_smallz

def reducedMomentUpper (z : ℝ) : ℝ :=
    (1 / g (4323618/10000000) 0) *
        (trialGroupMultR grpAe (4323618/10000000) 15 z *
            powerArcStieltjes (4323618/10000000) 15 z
          + trialGroupRestR grpAe (4323618/10000000) 15 z
          + (trialGroupMultR grpAo (4323618/10000000) 14 z *
              powerArcStieltjes (4323618/10000000) 14 z
            + trialGroupRestR grpAo (4323618/10000000) 14 z))
      + (1 / g (5676382/10000000) 0) *
        (trialGroupMultR grpBe (5676382/10000000) 15 z *
            powerArcStieltjes (5676382/10000000) 15 z
          + trialGroupRestR grpBe (5676382/10000000) 15 z
          + (trialGroupMultR grpBo (5676382/10000000) 14 z *
              powerArcStieltjes (5676382/10000000) 14 z
            + trialGroupRestR grpBo (5676382/10000000) 14 z))

theorem reducedMomentUpper_eq :
    (∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
      powerArcStieltjes (exponent i) (9 + shift i) (14/3)) =
      reducedMomentUpper (14/3) := by
  exact stieltjes_side_reduced_refl (14/3) (by norm_num) denom_smallzR

end KsIndex.OppositeHalf

namespace KsIndex.AlphaRemarkTrial
open OppositeHalf

/-- The signed moment has only the eight certified base transforms left to evaluate. -/
theorem signedTrialMoment_eq_reduced : signedTrialMoment = trialMomentPrefix +
    (reducedMomentUpper (14/3) + reducedMomentLower (13/3)) / 6 := by
  rw [signedTrialMoment_eq_transforms, reducedMomentUpper_eq, reducedMomentLower_eq]

end KsIndex.AlphaRemarkTrial
