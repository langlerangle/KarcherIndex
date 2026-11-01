module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache17152
public import KsIndexLean.AlphaLowSampleCache17408

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm143 : Finset ℤ := Finset.Ioc (959) (1023)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm143
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm143)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (1023) then Cache17152.entries[(n - (767)).toNat]?.getD (0, 0)
  else Cache17408.entries[(n - (1023)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm143) : (959) < n ∧ n ≤ (1023) := by
  simpa only [wMm143, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm143) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm143) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm143) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (1023)
  · have hi : (n - (767)).toNat < 256 := by omega
    have hm : 2 * Cache17152.mode (n - (767)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache17152.mode]
      omega
    have hc := Cache17152.checked ⟨(n - (767)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (1023)).toNat < 256 := by omega
    have hm : 2 * Cache17408.mode (n - (1023)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache17408.mode]
      omega
    have hc := Cache17408.checked ⟨(n - (1023)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm143) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm143) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm143_c_fast : tableEnergyNumerator t wMm143 4 1 = (18397678418560710916225540068833497726939174793258607335518466051897150463538773023275520507323388 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm143 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm143 4 1 =
      ∑ n ∈ wMm143, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm143_r_fast : tableEnergyRadius t wMm143 4 1 = (63337208608356188565644116331792428380805456476802300894970254132280339960418135999185321 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm143 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm143 4 1 =
      ∑ n ∈ wMm143, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm143

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm143_c : tableEnergyNumerator t wMm143 4 1 = (18397678418560710916225540068833497726939174793258607335518466051897150463538773023275520507323388 : ℤ) := by
  exact KsIndex.NegSignProdFastMm143.eMm143_c_fast
theorem eMm143_r : tableEnergyRadius t wMm143 4 1 = (63337208608356188565644116331792428380805456476802300894970254132280339960418135999185321 : ℤ) := by
  exact KsIndex.NegSignProdFastMm143.eMm143_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm143_c
#print axioms KsIndex.NegSignProd.eMm143_r
