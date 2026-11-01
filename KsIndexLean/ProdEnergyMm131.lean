module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache16384
public import KsIndexLean.AlphaLowSampleCache16640

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm131 : Finset ℤ := Finset.Ioc (191) (255)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm131
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm131)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (255) then Cache16384.entries[(n - (-1)).toNat]?.getD (0, 0)
  else Cache16640.entries[(n - (255)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm131) : (191) < n ∧ n ≤ (255) := by
  simpa only [wMm131, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm131) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm131) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm131) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (255)
  · have hi : (n - (-1)).toNat < 256 := by omega
    have hm : 2 * Cache16384.mode (n - (-1)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache16384.mode]
      omega
    have hc := Cache16384.checked ⟨(n - (-1)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (255)).toNat < 256 := by omega
    have hm : 2 * Cache16640.mode (n - (255)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache16640.mode]
      omega
    have hc := Cache16640.checked ⟨(n - (255)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm131) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm131) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm131_c_fast : tableEnergyNumerator t wMm131 4 1 = (355978115137747902355704238317877916029210656896343815683755543786749580192926198654842536420046402 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm131 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm131 4 1 =
      ∑ n ∈ wMm131, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm131_r_fast : tableEnergyRadius t wMm131 4 1 = (1329967355039689241862845563929889263168505523666082684505333242286745409952704535970362078 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm131 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm131 4 1 =
      ∑ n ∈ wMm131, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm131

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm131_c : tableEnergyNumerator t wMm131 4 1 = (355978115137747902355704238317877916029210656896343815683755543786749580192926198654842536420046402 : ℤ) := by
  exact KsIndex.NegSignProdFastMm131.eMm131_c_fast
theorem eMm131_r : tableEnergyRadius t wMm131 4 1 = (1329967355039689241862845563929889263168505523666082684505333242286745409952704535970362078 : ℤ) := by
  exact KsIndex.NegSignProdFastMm131.eMm131_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm131_c
#print axioms KsIndex.NegSignProd.eMm131_r
