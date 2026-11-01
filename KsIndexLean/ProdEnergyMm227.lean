module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache22528
public import KsIndexLean.AlphaLowSampleCache22784

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm227 : Finset ℤ := Finset.Ioc (6335) (6399)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm227
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm227)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (6399) then Cache22528.entries[(n - (6143)).toNat]?.getD (0, 0)
  else Cache22784.entries[(n - (6399)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm227) : (6335) < n ∧ n ≤ (6399) := by
  simpa only [wMm227, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm227) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm227) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm227) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (6399)
  · have hi : (n - (6143)).toNat < 256 := by omega
    have hm : 2 * Cache22528.mode (n - (6143)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache22528.mode]
      omega
    have hc := Cache22528.checked ⟨(n - (6143)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (6399)).toNat < 256 := by omega
    have hm : 2 * Cache22784.mode (n - (6399)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache22784.mode]
      omega
    have hc := Cache22784.checked ⟨(n - (6399)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm227) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm227) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm227_c_fast : tableEnergyNumerator t wMm227 4 1 = (476793959887971265223991415035932334237855064593560625295810150555472671583300775429746484275938 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm227 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm227 4 1 =
      ∑ n ∈ wMm227, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm227_r_fast : tableEnergyRadius t wMm227 4 1 = (1478486090162915012093612257814482131974096082287409697990650220025386006595875656298059 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm227 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm227 4 1 =
      ∑ n ∈ wMm227, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm227

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm227_c : tableEnergyNumerator t wMm227 4 1 = (476793959887971265223991415035932334237855064593560625295810150555472671583300775429746484275938 : ℤ) := by
  exact KsIndex.NegSignProdFastMm227.eMm227_c_fast
theorem eMm227_r : tableEnergyRadius t wMm227 4 1 = (1478486090162915012093612257814482131974096082287409697990650220025386006595875656298059 : ℤ) := by
  exact KsIndex.NegSignProdFastMm227.eMm227_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm227_c
#print axioms KsIndex.NegSignProd.eMm227_r
