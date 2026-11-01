module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache15360
public import KsIndexLean.AlphaLowSampleCache15616

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm115 : Finset ℤ := Finset.Ioc (-833) (-769)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm115
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm115)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-769) then Cache15360.entries[(n - (-1025)).toNat]?.getD (0, 0)
  else Cache15616.entries[(n - (-769)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm115) : (-833) < n ∧ n ≤ (-769) := by
  simpa only [wMm115, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm115) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm115) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm115) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-769)
  · have hi : (n - (-1025)).toNat < 256 := by omega
    have hm : 2 * Cache15360.mode (n - (-1025)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache15360.mode]
      omega
    have hc := Cache15360.checked ⟨(n - (-1025)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-769)).toNat < 256 := by omega
    have hm : 2 * Cache15616.mode (n - (-769)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache15616.mode]
      omega
    have hc := Cache15616.checked ⟨(n - (-769)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm115) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm115) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm115_c_fast : tableEnergyNumerator t wMm115 4 1 = (1024637044714194226190622669626769548513528682182420483912381946878738817335183388051810622866053 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm115 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm115 4 1 =
      ∑ n ∈ wMm115, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm115_r_fast : tableEnergyRadius t wMm115 4 1 = (18701617676353814894984371347365814154055192503691710224148857543964762989049324672144812 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm115 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm115 4 1 =
      ∑ n ∈ wMm115, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm115

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm115_c : tableEnergyNumerator t wMm115 4 1 = (1024637044714194226190622669626769548513528682182420483912381946878738817335183388051810622866053 : ℤ) := by
  exact KsIndex.NegSignProdFastMm115.eMm115_c_fast
theorem eMm115_r : tableEnergyRadius t wMm115 4 1 = (18701617676353814894984371347365814154055192503691710224148857543964762989049324672144812 : ℤ) := by
  exact KsIndex.NegSignProdFastMm115.eMm115_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm115_c
#print axioms KsIndex.NegSignProd.eMm115_r
