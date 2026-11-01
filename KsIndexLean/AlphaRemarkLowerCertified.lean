module

public import KsIndexLean.AlphaRemarkLowerWithMoments
public import KsIndexLean.AlphaActualRemainderIdentity
public import KsIndexLean.AlphaActualOuterBounds

@[expose] public section


/-! Optional complete numerical lower bound, retaining the production-certificate
build boundary. This proof has no residual identity or estimate premises. -/
namespace KsIndex.AlphaRemarkTrial.LowerAssembly

theorem alphaStar_gt_4323617 :
    (4323617 / 10000000 : ℝ) < Staircase.alphaStar := by
  apply alphaStar_lower_with_moments
  · intro neg n hn _
    simpa only [actualMoment] using MiddleInterval.raw_eq_remainderValue neg n hn
  · exact rawRemainder_outer_certified
  · exact rawRemainderNegative_outer_certified

end KsIndex.AlphaRemarkTrial.LowerAssembly
#print axioms KsIndex.AlphaRemarkTrial.LowerAssembly.alphaStar_gt_4323617
