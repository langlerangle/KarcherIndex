module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache8192
public import KsIndexLean.AlphaLowSampleCache8448

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm3 : Finset ℤ := Finset.Ioc (-8001) (-7937)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm3
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm3)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-7937) then Cache8192.entries[(n - (-8193)).toNat]?.getD (0, 0)
  else Cache8448.entries[(n - (-7937)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm3) : (-8001) < n ∧ n ≤ (-7937) := by
  simpa only [wMm3, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm3) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm3) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm3) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-7937)
  · have hi : (n - (-8193)).toNat < 256 := by omega
    have hm : 2 * Cache8192.mode (n - (-8193)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache8192.mode]
      omega
    have hc := Cache8192.checked ⟨(n - (-8193)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-7937)).toNat < 256 := by omega
    have hm : 2 * Cache8448.mode (n - (-7937)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache8448.mode]
      omega
    have hc := Cache8448.checked ⟨(n - (-7937)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm3) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm3) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm3_c_fast : tableEnergyNumerator t wMm3 4 1 = (34568802508173839805340539596206614723518411404261910725795801770948154447278269771175626818249 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm3 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm3 4 1 =
      ∑ n ∈ wMm3, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm3_r_fast : tableEnergyRadius t wMm3 4 1 = (315674175633831587759755801783694526453479135748856524491073465497399805182336913279728 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm3 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm3 4 1 =
      ∑ n ∈ wMm3, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm3

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm3_c : tableEnergyNumerator t wMm3 4 1 = (34568802508173839805340539596206614723518411404261910725795801770948154447278269771175626818249 : ℤ) := by
  exact KsIndex.NegSignProdFastMm3.eMm3_c_fast
theorem eMm3_r : tableEnergyRadius t wMm3 4 1 = (315674175633831587759755801783694526453479135748856524491073465497399805182336913279728 : ℤ) := by
  exact KsIndex.NegSignProdFastMm3.eMm3_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm3_c
#print axioms KsIndex.NegSignProd.eMm3_r
