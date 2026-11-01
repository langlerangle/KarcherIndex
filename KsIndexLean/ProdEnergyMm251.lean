module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache24064
public import KsIndexLean.AlphaLowSampleCache24320

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm251 : Finset ℤ := Finset.Ioc (7871) (7935)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm251
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm251)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (7935) then Cache24064.entries[(n - (7679)).toNat]?.getD (0, 0)
  else Cache24320.entries[(n - (7935)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm251) : (7871) < n ∧ n ≤ (7935) := by
  simpa only [wMm251, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm251) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm251) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm251) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (7935)
  · have hi : (n - (7679)).toNat < 256 := by omega
    have hm : 2 * Cache24064.mode (n - (7679)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache24064.mode]
      omega
    have hc := Cache24064.checked ⟨(n - (7679)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (7935)).toNat < 256 := by omega
    have hm : 2 * Cache24320.mode (n - (7935)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache24320.mode]
      omega
    have hc := Cache24320.checked ⟨(n - (7935)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm251) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm251) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm251_c_fast : tableEnergyNumerator t wMm251 4 1 = (312472406410438452133755861507853662668562869430209540139636834661076456123828267057503773115319 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm251 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm251 4 1 =
      ∑ n ∈ wMm251, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm251_r_fast : tableEnergyRadius t wMm251 4 1 = (957051439733934868167601257136883113002608006705518700653207938760038096684750931625870 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm251 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm251 4 1 =
      ∑ n ∈ wMm251, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm251

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm251_c : tableEnergyNumerator t wMm251 4 1 = (312472406410438452133755861507853662668562869430209540139636834661076456123828267057503773115319 : ℤ) := by
  exact KsIndex.NegSignProdFastMm251.eMm251_c_fast
theorem eMm251_r : tableEnergyRadius t wMm251 4 1 = (957051439733934868167601257136883113002608006705518700653207938760038096684750931625870 : ℤ) := by
  exact KsIndex.NegSignProdFastMm251.eMm251_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm251_c
#print axioms KsIndex.NegSignProd.eMm251_r
