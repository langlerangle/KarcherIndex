module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache15104
public import KsIndexLean.AlphaLowSampleCache15360

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm111 : Finset ℤ := Finset.Ioc (-1089) (-1025)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm111
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm111)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-1025) then Cache15104.entries[(n - (-1281)).toNat]?.getD (0, 0)
  else Cache15360.entries[(n - (-1025)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm111) : (-1089) < n ∧ n ≤ (-1025) := by
  simpa only [wMm111, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm111) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm111) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm111) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-1025)
  · have hi : (n - (-1281)).toNat < 256 := by omega
    have hm : 2 * Cache15104.mode (n - (-1281)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache15104.mode]
      omega
    have hc := Cache15104.checked ⟨(n - (-1281)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-1025)).toNat < 256 := by omega
    have hm : 2 * Cache15360.mode (n - (-1025)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache15360.mode]
      omega
    have hc := Cache15360.checked ⟨(n - (-1025)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm111) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm111) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm111_c_fast : tableEnergyNumerator t wMm111 4 1 = (709517367892386094027550899726377213482305365146284282171670061426399171087902793705208163636393 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm111 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm111 4 1 =
      ∑ n ∈ wMm111, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm111_r_fast : tableEnergyRadius t wMm111 4 1 = (11651624776955615179597672381626314915179271987327896980820996579420989912100582254777349 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm111 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm111 4 1 =
      ∑ n ∈ wMm111, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm111

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm111_c : tableEnergyNumerator t wMm111 4 1 = (709517367892386094027550899726377213482305365146284282171670061426399171087902793705208163636393 : ℤ) := by
  exact KsIndex.NegSignProdFastMm111.eMm111_c_fast
theorem eMm111_r : tableEnergyRadius t wMm111 4 1 = (11651624776955615179597672381626314915179271987327896980820996579420989912100582254777349 : ℤ) := by
  exact KsIndex.NegSignProdFastMm111.eMm111_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm111_c
#print axioms KsIndex.NegSignProd.eMm111_r
