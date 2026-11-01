module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache11776
public import KsIndexLean.AlphaLowSampleCache12032

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm59 : Finset ℤ := Finset.Ioc (-4417) (-4353)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm59
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm59)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-4353) then Cache11776.entries[(n - (-4609)).toNat]?.getD (0, 0)
  else Cache12032.entries[(n - (-4353)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm59) : (-4417) < n ∧ n ≤ (-4353) := by
  simpa only [wMm59, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm59) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm59) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm59) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-4353)
  · have hi : (n - (-4609)).toNat < 256 := by omega
    have hm : 2 * Cache11776.mode (n - (-4609)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache11776.mode]
      omega
    have hc := Cache11776.checked ⟨(n - (-4609)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-4353)).toNat < 256 := by omega
    have hm : 2 * Cache12032.mode (n - (-4353)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache12032.mode]
      omega
    have hc := Cache12032.checked ⟨(n - (-4353)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm59) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm59) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm59_c_fast : tableEnergyNumerator t wMm59 4 1 = (88478308705092714645156415101474028767006165066439010354447964241974370692601182104858235188660 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm59 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm59 4 1 =
      ∑ n ∈ wMm59, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm59_r_fast : tableEnergyRadius t wMm59 4 1 = (937589037358236755130584750262627195294119073855559207528633394778361118066731881829489 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm59 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm59 4 1 =
      ∑ n ∈ wMm59, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm59

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm59_c : tableEnergyNumerator t wMm59 4 1 = (88478308705092714645156415101474028767006165066439010354447964241974370692601182104858235188660 : ℤ) := by
  exact KsIndex.NegSignProdFastMm59.eMm59_c_fast
theorem eMm59_r : tableEnergyRadius t wMm59 4 1 = (937589037358236755130584750262627195294119073855559207528633394778361118066731881829489 : ℤ) := by
  exact KsIndex.NegSignProdFastMm59.eMm59_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm59_c
#print axioms KsIndex.NegSignProd.eMm59_r
