module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache21248
public import KsIndexLean.AlphaLowSampleCache21504

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm207 : Finset ℤ := Finset.Ioc (5055) (5119)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm207
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm207)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (5119) then Cache21248.entries[(n - (4863)).toNat]?.getD (0, 0)
  else Cache21504.entries[(n - (5119)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm207) : (5055) < n ∧ n ≤ (5119) := by
  simpa only [wMm207, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm207) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm207) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm207) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (5119)
  · have hi : (n - (4863)).toNat < 256 := by omega
    have hm : 2 * Cache21248.mode (n - (4863)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache21248.mode]
      omega
    have hc := Cache21248.checked ⟨(n - (4863)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (5119)).toNat < 256 := by omega
    have hm : 2 * Cache21504.mode (n - (5119)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache21504.mode]
      omega
    have hc := Cache21504.checked ⟨(n - (5119)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm207) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm207) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm207_c_fast : tableEnergyNumerator t wMm207 4 1 = (739759186868685196397407515657171279591607070983422594814493820694515526243422596729334451512991 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm207 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm207 4 1 =
      ∑ n ∈ wMm207, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm207_r_fast : tableEnergyRadius t wMm207 4 1 = (2323435949436656225235685527354130241068165253654654863667039106592803401150231410131327 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm207 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm207 4 1 =
      ∑ n ∈ wMm207, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm207

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm207_c : tableEnergyNumerator t wMm207 4 1 = (739759186868685196397407515657171279591607070983422594814493820694515526243422596729334451512991 : ℤ) := by
  exact KsIndex.NegSignProdFastMm207.eMm207_c_fast
theorem eMm207_r : tableEnergyRadius t wMm207 4 1 = (2323435949436656225235685527354130241068165253654654863667039106592803401150231410131327 : ℤ) := by
  exact KsIndex.NegSignProdFastMm207.eMm207_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm207_c
#print axioms KsIndex.NegSignProd.eMm207_r
