module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache14848
public import KsIndexLean.AlphaLowSampleCache15104

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm107 : Finset ℤ := Finset.Ioc (-1345) (-1281)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm107
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm107)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-1281) then Cache14848.entries[(n - (-1537)).toNat]?.getD (0, 0)
  else Cache15104.entries[(n - (-1281)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm107) : (-1345) < n ∧ n ≤ (-1281) := by
  simpa only [wMm107, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm107) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm107) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm107) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-1281)
  · have hi : (n - (-1537)).toNat < 256 := by omega
    have hm : 2 * Cache14848.mode (n - (-1537)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache14848.mode]
      omega
    have hc := Cache14848.checked ⟨(n - (-1537)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-1281)).toNat < 256 := by omega
    have hm : 2 * Cache15104.mode (n - (-1281)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache15104.mode]
      omega
    have hc := Cache15104.checked ⟨(n - (-1281)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm107) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm107) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm107_c_fast : tableEnergyNumerator t wMm107 4 1 = (526569204012188811811922311790173163644873803188355649081039083009739419186920567415757451154639 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm107 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm107 4 1 =
      ∑ n ∈ wMm107, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm107_r_fast : tableEnergyRadius t wMm107 4 1 = (8007093306542387428552150057427416372368866168333102485062349287216078836690956224915045 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm107 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm107 4 1 =
      ∑ n ∈ wMm107, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm107

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm107_c : tableEnergyNumerator t wMm107 4 1 = (526569204012188811811922311790173163644873803188355649081039083009739419186920567415757451154639 : ℤ) := by
  exact KsIndex.NegSignProdFastMm107.eMm107_c_fast
theorem eMm107_r : tableEnergyRadius t wMm107 4 1 = (8007093306542387428552150057427416372368866168333102485062349287216078836690956224915045 : ℤ) := by
  exact KsIndex.NegSignProdFastMm107.eMm107_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm107_c
#print axioms KsIndex.NegSignProd.eMm107_r
