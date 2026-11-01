module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache17408
public import KsIndexLean.AlphaLowSampleCache17664

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm147 : Finset ℤ := Finset.Ioc (1215) (1279)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm147
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm147)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (1279) then Cache17408.entries[(n - (1023)).toNat]?.getD (0, 0)
  else Cache17664.entries[(n - (1279)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm147) : (1215) < n ∧ n ≤ (1279) := by
  simpa only [wMm147, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm147) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm147) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm147) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (1279)
  · have hi : (n - (1023)).toNat < 256 := by omega
    have hm : 2 * Cache17408.mode (n - (1023)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache17408.mode]
      omega
    have hc := Cache17408.checked ⟨(n - (1023)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (1279)).toNat < 256 := by omega
    have hm : 2 * Cache17664.mode (n - (1279)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache17664.mode]
      omega
    have hc := Cache17664.checked ⟨(n - (1279)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm147) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm147) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm147_c_fast : tableEnergyNumerator t wMm147 4 1 = (11697526810728720590425977354796907506017991908531477440680090169503837320566656191442401283228594 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm147 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm147 4 1 =
      ∑ n ∈ wMm147, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm147_r_fast : tableEnergyRadius t wMm147 4 1 = (39761707854546124477033135784105725919564346098736660263326752148273054932195456969907171 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm147 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm147 4 1 =
      ∑ n ∈ wMm147, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm147

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm147_c : tableEnergyNumerator t wMm147 4 1 = (11697526810728720590425977354796907506017991908531477440680090169503837320566656191442401283228594 : ℤ) := by
  exact KsIndex.NegSignProdFastMm147.eMm147_c_fast
theorem eMm147_r : tableEnergyRadius t wMm147 4 1 = (39761707854546124477033135784105725919564346098736660263326752148273054932195456969907171 : ℤ) := by
  exact KsIndex.NegSignProdFastMm147.eMm147_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm147_c
#print axioms KsIndex.NegSignProd.eMm147_r
