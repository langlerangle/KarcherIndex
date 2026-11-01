module

public import KsIndexLean.AlphaMomentNormalized

@[expose] public section

noncomputable section
namespace KsIndex.OppositeHalf
open KsIndex.AlphaRemarkTrial
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem lower_grpAe_multiplier :
    trialGroupMult grpAe (2161809/5000000) 15 (13/3) =
      (-373337434294432990534995648772099054608532428981/498807821285503305195227429169041268079053737500 : ℝ) := by
  norm_num [trialGroupMult, trialGroupMultR, zChainCoeff, grpAe, grpAo, grpBe, grpBo,
    exponent, coefficient, shift, chainLen, chainLenR, baseShift, Int.toNat,
    Finset.sum_filter, Fin.sum_univ_succ]

theorem lower_grpAo_multiplier :
    trialGroupMult grpAo (2161809/5000000) 14 (13/3) =
      (291663184609238360386059556369153927282419/246209462374071752260912394228174685050000 : ℝ) := by
  norm_num [trialGroupMult, trialGroupMultR, zChainCoeff, grpAe, grpAo, grpBe, grpBo,
    exponent, coefficient, shift, chainLen, chainLenR, baseShift, Int.toNat,
    Finset.sum_filter, Fin.sum_univ_succ]

theorem lower_grpBe_multiplier :
    trialGroupMult grpBe (2838191/5000000) 15 (13/3) =
      (13593553256999717408970713924408326315572660700941876600123/1046652058545128339523428745288795575439567289000000000000 : ℝ) := by
  norm_num [trialGroupMult, trialGroupMultR, zChainCoeff, grpAe, grpAo, grpBe, grpBo,
    exponent, coefficient, shift, chainLen, chainLenR, baseShift, Int.toNat,
    Finset.sum_filter, Fin.sum_univ_succ]

theorem lower_grpBo_multiplier :
    trialGroupMult grpBo (2838191/5000000) 14 (13/3) =
      (4409011793609857095390155347780584324534583968327/300027369651819522655410888841344143687500000000 : ℝ) := by
  norm_num [trialGroupMult, trialGroupMultR, zChainCoeff, grpAe, grpAo, grpBe, grpBo,
    exponent, coefficient, shift, chainLen, chainLenR, baseShift, Int.toNat,
    Finset.sum_filter, Fin.sum_univ_succ]

theorem upper_grpAe_multiplier :
    trialGroupMultR grpAe (2161809/5000000) 15 (14/3) =
      (-373337434294432990534995648772099054608532428981/3528313374603553813618629063121504170829053737500 : ℝ) := by
  norm_num [trialGroupMult, trialGroupMultR, zChainCoeff, grpAe, grpAo, grpBe, grpBo,
    exponent, coefficient, shift, chainLen, chainLenR, baseShift, Int.toNat,
    Finset.sum_filter, Fin.sum_univ_succ]

theorem upper_grpAo_multiplier :
    trialGroupMultR grpAo (2161809/5000000) 14 (14/3) =
      (291663184609238360386059556369153927282419/108859053108488240032934852885674685050000 : ℝ) := by
  norm_num [trialGroupMult, trialGroupMultR, zChainCoeff, grpAe, grpAo, grpBe, grpBo,
    exponent, coefficient, shift, chainLen, chainLenR, baseShift, Int.toNat,
    Finset.sum_filter, Fin.sum_univ_succ]

theorem upper_grpBe_multiplier :
    trialGroupMultR grpBe (2838191/5000000) 15 (14/3) =
      (13593553256999717408970713924408326315572660700941876600123/3429485839056939492271439244664128221019567289000000000000 : ℝ) := by
  norm_num [trialGroupMult, trialGroupMultR, zChainCoeff, grpAe, grpAo, grpBe, grpBo,
    exponent, coefficient, shift, chainLen, chainLenR, baseShift, Int.toNat,
    Finset.sum_filter, Fin.sum_univ_succ]

theorem upper_grpBo_multiplier :
    trialGroupMultR grpBo (2838191/5000000) 14 (14/3) =
      (4409011793609857095390155347780584324534583968327/61672076276599065894126462163219143687500000000 : ℝ) := by
  norm_num [trialGroupMult, trialGroupMultR, zChainCoeff, grpAe, grpAo, grpBe, grpBo,
    exponent, coefficient, shift, chainLen, chainLenR, baseShift, Int.toNat,
    Finset.sum_filter, Fin.sum_univ_succ]

end KsIndex.OppositeHalf
#print axioms KsIndex.OppositeHalf.lower_grpAe_multiplier
#print axioms KsIndex.OppositeHalf.lower_grpAo_multiplier
#print axioms KsIndex.OppositeHalf.lower_grpBe_multiplier
#print axioms KsIndex.OppositeHalf.lower_grpBo_multiplier
#print axioms KsIndex.OppositeHalf.upper_grpAe_multiplier
#print axioms KsIndex.OppositeHalf.upper_grpAo_multiplier
#print axioms KsIndex.OppositeHalf.upper_grpBe_multiplier
#print axioms KsIndex.OppositeHalf.upper_grpBo_multiplier
