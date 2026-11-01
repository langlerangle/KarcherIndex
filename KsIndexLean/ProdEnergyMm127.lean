module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache16128
public import KsIndexLean.AlphaLowSampleCache16384

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm127 : Finset ℤ := Finset.Ioc (-65) (-1)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm127
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm127)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-1) then Cache16128.entries[(n - (-257)).toNat]?.getD (0, 0)
  else Cache16384.entries[(n - (-1)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm127) : (-65) < n ∧ n ≤ (-1) := by
  simpa only [wMm127, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm127) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm127) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm127) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-1)
  · have hi : (n - (-257)).toNat < 256 := by omega
    have hm : 2 * Cache16128.mode (n - (-257)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache16128.mode]
      omega
    have hc := Cache16128.checked ⟨(n - (-257)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-1)).toNat < 256 := by omega
    have hm : 2 * Cache16384.mode (n - (-1)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache16384.mode]
      omega
    have hc := Cache16384.checked ⟨(n - (-1)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm127) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm127) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm127_c_fast : tableEnergyNumerator t wMm127 4 1 = (6951262644557965972127843338874322790676187012668876645625062207054521683635927775523248857475611444 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm127 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm127 4 1 =
      ∑ n ∈ wMm127, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm127_r_fast : tableEnergyRadius t wMm127 4 1 = (473398355081867105119701203653754897392325480641596550947842567227807724522248821561316706778 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm127 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm127 4 1 =
      ∑ n ∈ wMm127, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm127

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm127_c : tableEnergyNumerator t wMm127 4 1 = (6951262644557965972127843338874322790676187012668876645625062207054521683635927775523248857475611444 : ℤ) := by
  exact KsIndex.NegSignProdFastMm127.eMm127_c_fast
theorem eMm127_r : tableEnergyRadius t wMm127 4 1 = (473398355081867105119701203653754897392325480641596550947842567227807724522248821561316706778 : ℤ) := by
  exact KsIndex.NegSignProdFastMm127.eMm127_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm127_c
#print axioms KsIndex.NegSignProd.eMm127_r
