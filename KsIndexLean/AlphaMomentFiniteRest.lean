module

public import KsIndexLean.AlphaMomentNormalized
public import KsIndexLean.AlphaGroupSeedError

@[expose] public section

noncomputable section
namespace KsIndex.OppositeHalf
open PowerArc KsIndex.AlphaRemarkTrial
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem lower_grpAe_rest0 :
    seededGroupRest grpAe (2161809/5000000) 15 (13/3) 0
      (fun i => (coefficient i).re) (fun i => 9-shift i) chainLen =
      (0/1 : ℝ) := by
  norm_num [seededGroupRest, integerSeedValue, normalizedCoefficient, zChainForceUnit,
    grpAe, grpAo, grpBe, grpBo, exponent, Finset.sum_filter, Fin.sum_univ_succ, coefficient, shift, chainLen, chainLenR, baseShift, Int.toNat, Finset.sum_range_succ, Finset.sum_insert, Finset.sum_singleton]

theorem lower_grpAe_rest1 :
    seededGroupRest grpAe (2161809/5000000) 15 (13/3) 1
      (fun i => (coefficient i).re) (fun i => 9-shift i) chainLen =
      (-2163548423842604049560761909249105491263085891228510334141595472340966714005966531620625607/173831369658632047049766042715867807038559282317364718868849039352125410698620947119410637500 : ℝ) := by
  norm_num [seededGroupRest, integerSeedValue, normalizedCoefficient, zChainForceUnit,
    grpAe, grpAo, grpBe, grpBo, exponent, Finset.sum_filter, Fin.sum_univ_succ, coefficient, shift, chainLen, chainLenR, baseShift, Int.toNat, Finset.sum_range_succ, Finset.sum_insert, Finset.sum_singleton]

theorem lower_grpAo_rest0 :
    seededGroupRest grpAo (2161809/5000000) 14 (13/3) 0
      (fun i => (coefficient i).re) (fun i => 9-shift i) chainLen =
      (-96101617989554922849445137096840856654717285918191019027871805887815717574561041401/4631307002104470102238989003452630357531497583077729490695178326624357993728065350000 : ℝ) := by
  norm_num [seededGroupRest, integerSeedValue, normalizedCoefficient, zChainForceUnit,
    grpAe, grpAo, grpBe, grpBo, exponent, Finset.sum_filter, Fin.sum_univ_succ, coefficient, shift, chainLen, chainLenR, baseShift, Int.toNat, Finset.sum_range_succ, Finset.sum_insert, Finset.sum_singleton]

theorem lower_grpAo_rest1 :
    seededGroupRest grpAo (2161809/5000000) 14 (13/3) 1
      (fun i => (coefficient i).re) (fun i => 9-shift i) chainLen =
      (-96101617989554922849445137096840856654717285918191019027871805887815717574561041401/4631307002104470102238989003452630357531497583077729490695178326624357993728065350000 : ℝ) := by
  norm_num [seededGroupRest, integerSeedValue, normalizedCoefficient, zChainForceUnit,
    grpAe, grpAo, grpBe, grpBo, exponent, Finset.sum_filter, Fin.sum_univ_succ, coefficient, shift, chainLen, chainLenR, baseShift, Int.toNat, Finset.sum_range_succ, Finset.sum_insert, Finset.sum_singleton]

theorem lower_grpBe_rest0 :
    seededGroupRest grpBe (2838191/5000000) 15 (13/3) 0
      (fun i => (coefficient i).re) (fun i => 9-shift i) chainLen =
      (0/1 : ℝ) := by
  norm_num [seededGroupRest, integerSeedValue, normalizedCoefficient, zChainForceUnit,
    grpAe, grpAo, grpBe, grpBo, exponent, Finset.sum_filter, Fin.sum_univ_succ, coefficient, shift, chainLen, chainLenR, baseShift, Int.toNat, Finset.sum_range_succ, Finset.sum_insert, Finset.sum_singleton]

theorem lower_grpBe_rest1 :
    seededGroupRest grpBe (2838191/5000000) 15 (13/3) 1
      (fun i => (coefficient i).re) (fun i => 9-shift i) chainLen =
      (5543706316339814425233367977480521115374349412493061030681054633921246286515375024264824369991/41015283288075080814585732129508180186819627979564573151150343217200207825043939864508136100000 : ℝ) := by
  norm_num [seededGroupRest, integerSeedValue, normalizedCoefficient, zChainForceUnit,
    grpAe, grpAo, grpBe, grpBo, exponent, Finset.sum_filter, Fin.sum_univ_succ, coefficient, shift, chainLen, chainLenR, baseShift, Int.toNat, Finset.sum_range_succ, Finset.sum_insert, Finset.sum_singleton]

theorem lower_grpBo_rest0 :
    seededGroupRest grpBo (2838191/5000000) 14 (13/3) 0
      (fun i => (coefficient i).re) (fun i => 9-shift i) chainLen =
      (-11811450854008864202068613955489369157126897758769672683684212704837140078517254307/86957402175421820913320724519263127172432900755621928786558237652152593875365577500 : ℝ) := by
  norm_num [seededGroupRest, integerSeedValue, normalizedCoefficient, zChainForceUnit,
    grpAe, grpAo, grpBe, grpBo, exponent, Finset.sum_filter, Fin.sum_univ_succ, coefficient, shift, chainLen, chainLenR, baseShift, Int.toNat, Finset.sum_range_succ, Finset.sum_insert, Finset.sum_singleton]

theorem lower_grpBo_rest1 :
    seededGroupRest grpBo (2838191/5000000) 14 (13/3) 1
      (fun i => (coefficient i).re) (fun i => 9-shift i) chainLen =
      (-11811450854008864202068613955489369157126897758769672683684212704837140078517254307/86957402175421820913320724519263127172432900755621928786558237652152593875365577500 : ℝ) := by
  norm_num [seededGroupRest, integerSeedValue, normalizedCoefficient, zChainForceUnit,
    grpAe, grpAo, grpBe, grpBo, exponent, Finset.sum_filter, Fin.sum_univ_succ, coefficient, shift, chainLen, chainLenR, baseShift, Int.toNat, Finset.sum_range_succ, Finset.sum_insert, Finset.sum_singleton]

theorem upper_grpAe_rest0 :
    seededGroupRest grpAe (2161809/5000000) 15 (14/3) 0
      (fun i => (coefficient i).re) (fun i => 9+shift i) chainLenR =
      (0/1 : ℝ) := by
  norm_num [seededGroupRest, integerSeedValue, normalizedCoefficient, zChainForceUnit,
    grpAe, grpAo, grpBe, grpBo, exponent, Finset.sum_filter, Fin.sum_univ_succ, coefficient, shift, chainLen, chainLenR, baseShift, Int.toNat, Finset.sum_range_succ, Finset.sum_insert, Finset.sum_singleton]

theorem upper_grpAe_rest1 :
    seededGroupRest grpAe (2161809/5000000) 15 (14/3) 1
      (fun i => (coefficient i).re) (fun i => 9+shift i) chainLenR =
      (-2663880992777224706740403073588773705899144239433926625992162019216275866086033468379374393/1229594886687136463392331572658982701381027041753196120525305277425907780622837131869410637500 : ℝ) := by
  norm_num [seededGroupRest, integerSeedValue, normalizedCoefficient, zChainForceUnit,
    grpAe, grpAo, grpBe, grpBo, exponent, Finset.sum_filter, Fin.sum_univ_succ, coefficient, shift, chainLen, chainLenR, baseShift, Int.toNat, Finset.sum_range_succ, Finset.sum_insert, Finset.sum_singleton]

theorem upper_grpAo_rest0 :
    seededGroupRest grpAo (2161809/5000000) 14 (14/3) 0
      (fun i => (coefficient i).re) (fun i => 9+shift i) chainLenR =
      (-40365251277234930671364900015050387525272414478171272656768860107878682425438958599/2047686104516253071177072032807629704441623126006676926216100878747219096228065350000 : ℝ) := by
  norm_num [seededGroupRest, integerSeedValue, normalizedCoefficient, zChainForceUnit,
    grpAe, grpAo, grpBe, grpBo, exponent, Finset.sum_filter, Fin.sum_univ_succ, coefficient, shift, chainLen, chainLenR, baseShift, Int.toNat, Finset.sum_range_succ, Finset.sum_insert, Finset.sum_singleton]

theorem upper_grpAo_rest1 :
    seededGroupRest grpAo (2161809/5000000) 14 (14/3) 1
      (fun i => (coefficient i).re) (fun i => 9+shift i) chainLenR =
      (-40365251277234930671364900015050387525272414478171272656768860107878682425438958599/2047686104516253071177072032807629704441623126006676926216100878747219096228065350000 : ℝ) := by
  norm_num [seededGroupRest, integerSeedValue, normalizedCoefficient, zChainForceUnit,
    grpAe, grpAo, grpBe, grpBo, exponent, Finset.sum_filter, Fin.sum_univ_succ, coefficient, shift, chainLen, chainLenR, baseShift, Int.toNat, Finset.sum_range_succ, Finset.sum_insert, Finset.sum_singleton]

theorem upper_grpBe_rest0 :
    seededGroupRest grpBe (2838191/5000000) 15 (14/3) 0
      (fun i => (coefficient i).re) (fun i => 9+shift i) chainLenR =
      (0/1 : ℝ) := by
  norm_num [seededGroupRest, integerSeedValue, normalizedCoefficient, zChainForceUnit,
    grpAe, grpAo, grpBe, grpBo, exponent, Finset.sum_filter, Fin.sum_univ_succ, coefficient, shift, chainLen, chainLenR, baseShift, Int.toNat, Finset.sum_range_succ, Finset.sum_insert, Finset.sum_singleton]

theorem upper_grpBe_rest1 :
    seededGroupRest grpBe (2838191/5000000) 15 (14/3) 1
      (fun i => (coefficient i).re) (fun i => 9+shift i) chainLenR =
      (593228158516201150894250670453184092874470088237720301095905546811861602536406945273339488181/12217425862601880739483120078583435984384122555157788351333369000784115135862083236955285100000 : ℝ) := by
  norm_num [seededGroupRest, integerSeedValue, normalizedCoefficient, zChainForceUnit,
    grpAe, grpAo, grpBe, grpBo, exponent, Finset.sum_filter, Fin.sum_univ_succ, coefficient, shift, chainLen, chainLenR, baseShift, Int.toNat, Finset.sum_range_succ, Finset.sum_insert, Finset.sum_singleton]

theorem upper_grpBo_rest0 :
    seededGroupRest grpBo (2838191/5000000) 14 (14/3) 0
      (fun i => (coefficient i).re) (fun i => 9+shift i) chainLenR =
      (-78725496649919070553413094271685498192413615887102593897370545624691461307575780149/125121600812644230748512794440168920825478042168934020194440406773985285752559042500 : ℝ) := by
  norm_num [seededGroupRest, integerSeedValue, normalizedCoefficient, zChainForceUnit,
    grpAe, grpAo, grpBe, grpBo, exponent, Finset.sum_filter, Fin.sum_univ_succ, coefficient, shift, chainLen, chainLenR, baseShift, Int.toNat, Finset.sum_range_succ, Finset.sum_insert, Finset.sum_singleton]

theorem upper_grpBo_rest1 :
    seededGroupRest grpBo (2838191/5000000) 14 (14/3) 1
      (fun i => (coefficient i).re) (fun i => 9+shift i) chainLenR =
      (-78725496649919070553413094271685498192413615887102593897370545624691461307575780149/125121600812644230748512794440168920825478042168934020194440406773985285752559042500 : ℝ) := by
  norm_num [seededGroupRest, integerSeedValue, normalizedCoefficient, zChainForceUnit,
    grpAe, grpAo, grpBe, grpBo, exponent, Finset.sum_filter, Fin.sum_univ_succ, coefficient, shift, chainLen, chainLenR, baseShift, Int.toNat, Finset.sum_range_succ, Finset.sum_insert, Finset.sum_singleton]

end KsIndex.OppositeHalf
#print axioms KsIndex.OppositeHalf.lower_grpAe_rest0
#print axioms KsIndex.OppositeHalf.lower_grpAe_rest1
#print axioms KsIndex.OppositeHalf.lower_grpAo_rest0
#print axioms KsIndex.OppositeHalf.lower_grpAo_rest1
#print axioms KsIndex.OppositeHalf.lower_grpBe_rest0
#print axioms KsIndex.OppositeHalf.lower_grpBe_rest1
#print axioms KsIndex.OppositeHalf.lower_grpBo_rest0
#print axioms KsIndex.OppositeHalf.lower_grpBo_rest1
#print axioms KsIndex.OppositeHalf.upper_grpAe_rest0
#print axioms KsIndex.OppositeHalf.upper_grpAe_rest1
#print axioms KsIndex.OppositeHalf.upper_grpAo_rest0
#print axioms KsIndex.OppositeHalf.upper_grpAo_rest1
#print axioms KsIndex.OppositeHalf.upper_grpBe_rest0
#print axioms KsIndex.OppositeHalf.upper_grpBe_rest1
#print axioms KsIndex.OppositeHalf.upper_grpBo_rest0
#print axioms KsIndex.OppositeHalf.upper_grpBo_rest1
