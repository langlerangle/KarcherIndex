module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache14336
public import KsIndexLean.AlphaLowSampleCache14592

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm99 : Finset ℤ := Finset.Ioc (-1857) (-1793)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm99
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm99)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-1793) then Cache14336.entries[(n - (-2049)).toNat]?.getD (0, 0)
  else Cache14592.entries[(n - (-1793)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm99) : (-1857) < n ∧ n ≤ (-1793) := by
  simpa only [wMm99, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm99) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm99) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm99) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-1793)
  · have hi : (n - (-2049)).toNat < 256 := by omega
    have hm : 2 * Cache14336.mode (n - (-2049)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache14336.mode]
      omega
    have hc := Cache14336.checked ⟨(n - (-2049)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-1793)).toNat < 256 := by omega
    have hm : 2 * Cache14592.mode (n - (-1793)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache14592.mode]
      omega
    have hc := Cache14592.checked ⟨(n - (-1793)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm99) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm99) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm99_c_fast : tableEnergyNumerator t wMm99 4 1 = (329761864037772145672848299440186857764213344545874364368091419766123651025789695309078518038733 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm99 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm99 4 1 =
      ∑ n ∈ wMm99, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm99_r_fast : tableEnergyRadius t wMm99 4 1 = (4497937968694044281583089637833353057386254285487395617535308037225273284001345633417948 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm99 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm99 4 1 =
      ∑ n ∈ wMm99, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm99

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm99_c : tableEnergyNumerator t wMm99 4 1 = (329761864037772145672848299440186857764213344545874364368091419766123651025789695309078518038733 : ℤ) := by
  exact KsIndex.NegSignProdFastMm99.eMm99_c_fast
theorem eMm99_r : tableEnergyRadius t wMm99 4 1 = (4497937968694044281583089637833353057386254285487395617535308037225273284001345633417948 : ℤ) := by
  exact KsIndex.NegSignProdFastMm99.eMm99_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm99_c
#print axioms KsIndex.NegSignProd.eMm99_r
