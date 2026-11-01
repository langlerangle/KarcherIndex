module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache11008
public import KsIndexLean.AlphaLowSampleCache11264

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm47 : Finset ℤ := Finset.Ioc (-5185) (-5121)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm47
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm47)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-5121) then Cache11008.entries[(n - (-5377)).toNat]?.getD (0, 0)
  else Cache11264.entries[(n - (-5121)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm47) : (-5185) < n ∧ n ≤ (-5121) := by
  simpa only [wMm47, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm47) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm47) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm47) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-5121)
  · have hi : (n - (-5377)).toNat < 256 := by omega
    have hm : 2 * Cache11008.mode (n - (-5377)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache11008.mode]
      omega
    have hc := Cache11008.checked ⟨(n - (-5377)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-5121)).toNat < 256 := by omega
    have hm : 2 * Cache11264.mode (n - (-5121)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache11264.mode]
      omega
    have hc := Cache11264.checked ⟨(n - (-5121)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm47) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm47) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm47_c_fast : tableEnergyNumerator t wMm47 4 1 = (68839936038571584506347372637659245816862461596538232371586805714698155115241001729266206260428 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm47 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm47 4 1 =
      ∑ n ∈ wMm47, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm47_r_fast : tableEnergyRadius t wMm47 4 1 = (699627876859323067226483399508396384345761036155031337245709081349239710677590613612696 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm47 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm47 4 1 =
      ∑ n ∈ wMm47, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm47

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm47_c : tableEnergyNumerator t wMm47 4 1 = (68839936038571584506347372637659245816862461596538232371586805714698155115241001729266206260428 : ℤ) := by
  exact KsIndex.NegSignProdFastMm47.eMm47_c_fast
theorem eMm47_r : tableEnergyRadius t wMm47 4 1 = (699627876859323067226483399508396384345761036155031337245709081349239710677590613612696 : ℤ) := by
  exact KsIndex.NegSignProdFastMm47.eMm47_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm47_c
#print axioms KsIndex.NegSignProd.eMm47_r
