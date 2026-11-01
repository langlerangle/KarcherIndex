module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache22016
public import KsIndexLean.AlphaLowSampleCache22272

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm219 : Finset ℤ := Finset.Ioc (5823) (5887)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm219
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm219)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (5887) then Cache22016.entries[(n - (5631)).toNat]?.getD (0, 0)
  else Cache22272.entries[(n - (5887)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm219) : (5823) < n ∧ n ≤ (5887) := by
  simpa only [wMm219, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm219) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm219) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm219) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (5887)
  · have hi : (n - (5631)).toNat < 256 := by omega
    have hm : 2 * Cache22016.mode (n - (5631)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache22016.mode]
      omega
    have hc := Cache22016.checked ⟨(n - (5631)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (5887)).toNat < 256 := by omega
    have hm : 2 * Cache22272.mode (n - (5887)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache22272.mode]
      omega
    have hc := Cache22272.checked ⟨(n - (5887)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm219) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm219) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm219_c_fast : tableEnergyNumerator t wMm219 4 1 = (561775167411043284812322014730339558338131673682425623875228155566207829030072089210820240368679 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm219 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm219 4 1 =
      ∑ n ∈ wMm219, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm219_r_fast : tableEnergyRadius t wMm219 4 1 = (1750352239536995882143042554709260959394420829063208894128755991793374675903745115849058 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm219 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm219 4 1 =
      ∑ n ∈ wMm219, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm219

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm219_c : tableEnergyNumerator t wMm219 4 1 = (561775167411043284812322014730339558338131673682425623875228155566207829030072089210820240368679 : ℤ) := by
  exact KsIndex.NegSignProdFastMm219.eMm219_c_fast
theorem eMm219_r : tableEnergyRadius t wMm219 4 1 = (1750352239536995882143042554709260959394420829063208894128755991793374675903745115849058 : ℤ) := by
  exact KsIndex.NegSignProdFastMm219.eMm219_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm219_c
#print axioms KsIndex.NegSignProd.eMm219_r
