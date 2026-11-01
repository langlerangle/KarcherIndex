module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache14592
public import KsIndexLean.AlphaLowSampleCache14848

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm103 : Finset ℤ := Finset.Ioc (-1601) (-1537)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm103
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm103)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-1537) then Cache14592.entries[(n - (-1793)).toNat]?.getD (0, 0)
  else Cache14848.entries[(n - (-1537)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm103) : (-1601) < n ∧ n ≤ (-1537) := by
  simpa only [wMm103, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm103) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm103) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm103) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-1537)
  · have hi : (n - (-1793)).toNat < 256 := by omega
    have hm : 2 * Cache14592.mode (n - (-1793)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache14592.mode]
      omega
    have hc := Cache14592.checked ⟨(n - (-1793)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-1537)).toNat < 256 := by omega
    have hm : 2 * Cache14848.mode (n - (-1537)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache14848.mode]
      omega
    have hc := Cache14848.checked ⟨(n - (-1537)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm103) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm103) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm103_c_fast : tableEnergyNumerator t wMm103 4 1 = (409654808821911465735967109226101213067248762473994669769592011088171558396937686028301522788781 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm103 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm103 4 1 =
      ∑ n ∈ wMm103, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm103_r_fast : tableEnergyRadius t wMm103 4 1 = (5866981398814464824204935036109919841068277109096028829777377863902758571059991800424773 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm103 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm103 4 1 =
      ∑ n ∈ wMm103, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm103

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm103_c : tableEnergyNumerator t wMm103 4 1 = (409654808821911465735967109226101213067248762473994669769592011088171558396937686028301522788781 : ℤ) := by
  exact KsIndex.NegSignProdFastMm103.eMm103_c_fast
theorem eMm103_r : tableEnergyRadius t wMm103 4 1 = (5866981398814464824204935036109919841068277109096028829777377863902758571059991800424773 : ℤ) := by
  exact KsIndex.NegSignProdFastMm103.eMm103_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm103_c
#print axioms KsIndex.NegSignProd.eMm103_r
