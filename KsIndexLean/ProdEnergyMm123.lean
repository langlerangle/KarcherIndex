module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache15872
public import KsIndexLean.AlphaLowSampleCache16128

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm123 : Finset ℤ := Finset.Ioc (-321) (-257)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm123
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm123)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-257) then Cache15872.entries[(n - (-513)).toNat]?.getD (0, 0)
  else Cache16128.entries[(n - (-257)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm123) : (-321) < n ∧ n ≤ (-257) := by
  simpa only [wMm123, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm123) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm123) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm123) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-257)
  · have hi : (n - (-513)).toNat < 256 := by omega
    have hm : 2 * Cache15872.mode (n - (-513)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache15872.mode]
      omega
    have hc := Cache15872.checked ⟨(n - (-513)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-257)).toNat < 256 := by omega
    have hm : 2 * Cache16128.mode (n - (-257)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache16128.mode]
      omega
    have hc := Cache16128.checked ⟨(n - (-257)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm123) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm123) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm123_c_fast : tableEnergyNumerator t wMm123 4 1 = (3246134988099596578524732203867885677988464600520150082410471083449276114022606057208803800193276 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm123 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm123 4 1 =
      ∑ n ∈ wMm123, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm123_r_fast : tableEnergyRadius t wMm123 4 1 = (97106402593366391572401170758064583529248239033375835877765530156612500165480627991148591 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm123 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm123 4 1 =
      ∑ n ∈ wMm123, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm123

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm123_c : tableEnergyNumerator t wMm123 4 1 = (3246134988099596578524732203867885677988464600520150082410471083449276114022606057208803800193276 : ℤ) := by
  exact KsIndex.NegSignProdFastMm123.eMm123_c_fast
theorem eMm123_r : tableEnergyRadius t wMm123 4 1 = (97106402593366391572401170758064583529248239033375835877765530156612500165480627991148591 : ℤ) := by
  exact KsIndex.NegSignProdFastMm123.eMm123_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm123_c
#print axioms KsIndex.NegSignProd.eMm123_r
