module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache14080
public import KsIndexLean.AlphaLowSampleCache14336

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm95 : Finset ℤ := Finset.Ioc (-2113) (-2049)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm95
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm95)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-2049) then Cache14080.entries[(n - (-2305)).toNat]?.getD (0, 0)
  else Cache14336.entries[(n - (-2049)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm95) : (-2113) < n ∧ n ≤ (-2049) := by
  simpa only [wMm95, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm95) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm95) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm95) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-2049)
  · have hi : (n - (-2305)).toNat < 256 := by omega
    have hm : 2 * Cache14080.mode (n - (-2305)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache14080.mode]
      omega
    have hc := Cache14080.checked ⟨(n - (-2305)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-2049)).toNat < 256 := by omega
    have hm : 2 * Cache14336.mode (n - (-2049)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache14336.mode]
      omega
    have hc := Cache14336.checked ⟨(n - (-2049)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm95) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm95) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm95_c_fast : tableEnergyNumerator t wMm95 4 1 = (272402758360771314432802799072707317469808474194440224977354930882315307218284976922374350297813 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm95 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm95 4 1 =
      ∑ n ∈ wMm95, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm95_r_fast : tableEnergyRadius t wMm95 4 1 = (3566481136679217048208429407918405476981935232842163945321008286864602558406375751335427 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm95 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm95 4 1 =
      ∑ n ∈ wMm95, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm95

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm95_c : tableEnergyNumerator t wMm95 4 1 = (272402758360771314432802799072707317469808474194440224977354930882315307218284976922374350297813 : ℤ) := by
  exact KsIndex.NegSignProdFastMm95.eMm95_c_fast
theorem eMm95_r : tableEnergyRadius t wMm95 4 1 = (3566481136679217048208429407918405476981935232842163945321008286864602558406375751335427 : ℤ) := by
  exact KsIndex.NegSignProdFastMm95.eMm95_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm95_c
#print axioms KsIndex.NegSignProd.eMm95_r
