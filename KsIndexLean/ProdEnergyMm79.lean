module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache13056
public import KsIndexLean.AlphaLowSampleCache13312

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm79 : Finset ℤ := Finset.Ioc (-3137) (-3073)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm79
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm79)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-3073) then Cache13056.entries[(n - (-3329)).toNat]?.getD (0, 0)
  else Cache13312.entries[(n - (-3073)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm79) : (-3137) < n ∧ n ≤ (-3073) := by
  simpa only [wMm79, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm79) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm79) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm79) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-3073)
  · have hi : (n - (-3329)).toNat < 256 := by omega
    have hm : 2 * Cache13056.mode (n - (-3329)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache13056.mode]
      omega
    have hc := Cache13056.checked ⟨(n - (-3329)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-3073)).toNat < 256 := by omega
    have hm : 2 * Cache13312.mode (n - (-3073)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache13312.mode]
      omega
    have hc := Cache13312.checked ⟨(n - (-3073)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm79) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm79) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm79_c_fast : tableEnergyNumerator t wMm79 4 1 = (150080220579233795495965377200033532586339241288237040203829113649116709249022375547610937966058 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm79 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm79 4 1 =
      ∑ n ∈ wMm79, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm79_r_fast : tableEnergyRadius t wMm79 4 1 = (1746901345009941024940800518966854187816298296197507064258290298673392860892065810921831 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm79 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm79 4 1 =
      ∑ n ∈ wMm79, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm79

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm79_c : tableEnergyNumerator t wMm79 4 1 = (150080220579233795495965377200033532586339241288237040203829113649116709249022375547610937966058 : ℤ) := by
  exact KsIndex.NegSignProdFastMm79.eMm79_c_fast
theorem eMm79_r : tableEnergyRadius t wMm79 4 1 = (1746901345009941024940800518966854187816298296197507064258290298673392860892065810921831 : ℤ) := by
  exact KsIndex.NegSignProdFastMm79.eMm79_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm79_c
#print axioms KsIndex.NegSignProd.eMm79_r
