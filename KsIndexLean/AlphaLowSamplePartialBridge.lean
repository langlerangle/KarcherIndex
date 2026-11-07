module
public import KsIndexLean.AlphaLowSamplePartialReflection
public import KsIndexLean.AlphaLowSamplePartialRadius
public import KsIndexLean.AlphaLowProdAccessorFast
@[expose] public section
namespace KsIndex.SamplePartialSumProof
open KsIndex.AlphaRemarkTrial
/-- The exact numerator and radius equalities at one integer frequency. -/
def sampleClaim (k : ℤ) (p : ℤ × ℤ) : Prop :=
  p.1 = tableSampleNumerator KsIndex.PositiveEnergyAlphaLowProd.tFast k ∧
  p.2 = tableSampleRadius KsIndex.PositiveEnergyAlphaLowProd.tFast k
theorem from_parts (k a b r n p : ℤ)
    (ha : a = partialSumA KsIndex.PositiveEnergyAlphaLowProd.tFast k)
    (hb : b = partialSumB KsIndex.PositiveEnergyAlphaLowProd.tFast k)
    (hr : r = tableSampleRadius KsIndex.PositiveEnergyAlphaLowProd.tFast k)
    (hn : n = -a + b) (hp : p = a + b) :
    sampleClaim (-k) (n,r) ∧ sampleClaim k (p,r) := by
  constructor
  · constructor
    · calc
        n = -a + b := hn
        _ = -partialSumA KsIndex.PositiveEnergyAlphaLowProd.tFast k +
              partialSumB KsIndex.PositiveEnergyAlphaLowProd.tFast k := by rw [ha, hb]
        _ = tableSampleNumerator KsIndex.PositiveEnergyAlphaLowProd.tFast (-k) :=
          (tableSampleNumerator_neg_eq _ _).symm
    · calc
        r = tableSampleRadius KsIndex.PositiveEnergyAlphaLowProd.tFast k := hr
        _ = tableSampleRadius KsIndex.PositiveEnergyAlphaLowProd.tFast (-k) :=
          (KsIndex.SamplePartialSumRadius.radius_neg _ _).symm
  · constructor
    · calc
        p = a + b := hp
        _ = partialSumA KsIndex.PositiveEnergyAlphaLowProd.tFast k +
              partialSumB KsIndex.PositiveEnergyAlphaLowProd.tFast k := by rw [ha, hb]
        _ = tableSampleNumerator KsIndex.PositiveEnergyAlphaLowProd.tFast k := partialSum_add _ _
    · exact hr

end KsIndex.SamplePartialSumProof
