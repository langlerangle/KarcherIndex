module

public import KsIndexLean.AlphaLowModeCache
public import KsIndexLean.AlphaLowProdAccessorFast
public import KsIndexLean.AlphaLowTreeBackend

public import KsIndexLean.AlphaLowSamplePartialBlock0

@[expose] public section

/-! Exact sample-numerator and radius identities for the coefficient table.
Analytic enclosures follow when the table satisfies `ValidCoefficientTable`. -/
namespace KsIndex.AlphaRemarkTrial.Cache32768
open KsIndex.AlphaRemarkTrial
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
def mode (i : ℕ) : ℤ := -16385 + 32768 + (i : ℤ)
def entries : Array (ℤ × ℤ) := #[
(-109422911724474528648157092397035706083367222,160703531957702713985333684016640139),
(109413064976805358959620548198247484361173193,160688505818852369996556913743646969)
]
theorem checked0 :
 (entries[0]?.getD (0,0)).1 = tableSampleNumerator KsIndex.PositiveEnergyAlphaLowProd.tFast (2*mode 0+1) ∧
 (entries[0]?.getD (0,0)).2 = tableSampleRadius KsIndex.PositiveEnergyAlphaLowProd.tFast (2*mode 0+1) := by
  have h : entries[0]?.getD (0,0) = (-109422911724474528648157092397035706083367222,160703531957702713985333684016640139) := by decide +kernel
  have hk : 2*mode 0+1 = 32767 := by decide +kernel
  rw [hk]
  change KsIndex.SamplePartialSumProof.sampleClaim 32767 (entries[0]?.getD (0,0))
  rw [h]
  exact (KsIndex.SamplePartialSumProof.Block0.pair1).2
theorem checked1 :
 (entries[1]?.getD (0,0)).1 = tableSampleNumerator KsIndex.PositiveEnergyAlphaLowProd.tFast (2*mode 1+1) ∧
 (entries[1]?.getD (0,0)).2 = tableSampleRadius KsIndex.PositiveEnergyAlphaLowProd.tFast (2*mode 1+1) := by
  have h : entries[1]?.getD (0,0) = (109413064976805358959620548198247484361173193,160688505818852369996556913743646969) := by decide +kernel
  have hk : 2*mode 1+1 = 32769 := by decide +kernel
  rw [hk]
  change KsIndex.SamplePartialSumProof.sampleClaim 32769 (entries[1]?.getD (0,0))
  rw [h]
  exact (KsIndex.SamplePartialSumProof.Block0.pair0).2
theorem checked (i : Fin 2) :
 (entries[i.val]?.getD (0,0)).1 = tableSampleNumerator KsIndex.PositiveEnergyAlphaLowProd.tFast (2*mode i.val+1) ∧
 (entries[i.val]?.getD (0,0)).2 = tableSampleRadius KsIndex.PositiveEnergyAlphaLowProd.tFast (2*mode i.val+1) := by
  fin_cases i
  · exact checked0
  · exact checked1
#print axioms checked
end KsIndex.AlphaRemarkTrial.Cache32768
