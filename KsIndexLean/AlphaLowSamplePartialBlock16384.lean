module
public import KsIndexLean.AlphaLowSamplePartialBridge
public import KsIndexLean.AlphaLowTreeBackend
public import KsIndexLean.AlphaLowSamplePartialBlock15360

@[expose] public section
namespace KsIndex.SamplePartialSumProof.Block16384
open KsIndex.AlphaRemarkTrial
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
private theorem odd16384 : (-177287969887478979388231159888294017833282096204982 : ℤ) = partialSumA KsIndex.PositiveEnergyAlphaLowProd.tFast 1 := by
  rw [← KsIndex.AlphaLowTreeBackend.table_eq]
  decide +kernel

private theorem even16384 : (750147606155984539572254727698812921692964343005174 : ℤ) = partialSumB KsIndex.PositiveEnergyAlphaLowProd.tFast 1 := by
  rw [← KsIndex.AlphaLowTreeBackend.table_eq]
  decide +kernel

private theorem radius16384 : (1473765480947256256895754018045934436625151 : ℤ) = tableSampleRadius KsIndex.PositiveEnergyAlphaLowProd.tFast 1 := by
  rw [← KsIndex.AlphaLowTreeBackend.table_eq]
  decide +kernel

theorem pair16384 : sampleClaim (-1) (927435576043463518960485887587106939526246439210156,1473765480947256256895754018045934436625151) ∧ sampleClaim 1 (572859636268505560184023567810518903859682246800192,1473765480947256256895754018045934436625151) :=
  from_parts 1 (-177287969887478979388231159888294017833282096204982) (750147606155984539572254727698812921692964343005174) (1473765480947256256895754018045934436625151) (927435576043463518960485887587106939526246439210156) (572859636268505560184023567810518903859682246800192)
    odd16384 even16384 radius16384 (by decide +kernel) (by decide +kernel)
end KsIndex.SamplePartialSumProof.Block16384
