module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache23808
public import KsIndexLean.AlphaLowSampleCache24064

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm247 : Finset ℤ := Finset.Ioc (7615) (7679)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm247
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm247)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (7679) then Cache23808.entries[(n - (7423)).toNat]?.getD (0, 0)
  else Cache24064.entries[(n - (7679)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm247) : (7615) < n ∧ n ≤ (7679) := by
  simpa only [wMm247, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm247) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm247) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm247) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (7679)
  · have hi : (n - (7423)).toNat < 256 := by omega
    have hm : 2 * Cache23808.mode (n - (7423)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache23808.mode]
      omega
    have hc := Cache23808.checked ⟨(n - (7423)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (7679)).toNat < 256 := by omega
    have hm : 2 * Cache24064.mode (n - (7679)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache24064.mode]
      omega
    have hc := Cache24064.checked ⟨(n - (7679)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm247) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm247) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm247_c_fast : tableEnergyNumerator t wMm247 4 1 = (333245188582077888923931234928854031431595588585328364572565522663973881727171804860930287283668 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm247 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm247 4 1 =
      ∑ n ∈ wMm247, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm247_r_fast : tableEnergyRadius t wMm247 4 1 = (1022599375019572384242531911653410062798525624226514589453340781033684728143287456963831 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm247 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm247 4 1 =
      ∑ n ∈ wMm247, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm247

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm247_c : tableEnergyNumerator t wMm247 4 1 = (333245188582077888923931234928854031431595588585328364572565522663973881727171804860930287283668 : ℤ) := by
  exact KsIndex.NegSignProdFastMm247.eMm247_c_fast
theorem eMm247_r : tableEnergyRadius t wMm247 4 1 = (1022599375019572384242531911653410062798525624226514589453340781033684728143287456963831 : ℤ) := by
  exact KsIndex.NegSignProdFastMm247.eMm247_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm247_c
#print axioms KsIndex.NegSignProd.eMm247_r
