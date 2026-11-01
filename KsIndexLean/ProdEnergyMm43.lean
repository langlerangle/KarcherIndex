module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache10752
public import KsIndexLean.AlphaLowSampleCache11008

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm43 : Finset ℤ := Finset.Ioc (-5441) (-5377)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm43
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm43)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-5377) then Cache10752.entries[(n - (-5633)).toNat]?.getD (0, 0)
  else Cache11008.entries[(n - (-5377)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm43) : (-5441) < n ∧ n ≤ (-5377) := by
  simpa only [wMm43, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm43) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm43) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm43) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-5377)
  · have hi : (n - (-5633)).toNat < 256 := by omega
    have hm : 2 * Cache10752.mode (n - (-5633)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache10752.mode]
      omega
    have hc := Cache10752.checked ⟨(n - (-5633)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-5377)).toNat < 256 := by omega
    have hm : 2 * Cache11008.mode (n - (-5377)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache11008.mode]
      omega
    have hc := Cache11008.checked ⟨(n - (-5377)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm43) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm43) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm43_c_fast : tableEnergyNumerator t wMm43 4 1 = (63811810911344048244914071477933425537224171228596143546757467446575239649720641823897011523452 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm43 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm43 4 1 =
      ∑ n ∈ wMm43, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm43_r_fast : tableEnergyRadius t wMm43 4 1 = (640590263179318839335044904882836072552511680624986071596962124579929905082705802283332 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm43 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm43 4 1 =
      ∑ n ∈ wMm43, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm43

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm43_c : tableEnergyNumerator t wMm43 4 1 = (63811810911344048244914071477933425537224171228596143546757467446575239649720641823897011523452 : ℤ) := by
  exact KsIndex.NegSignProdFastMm43.eMm43_c_fast
theorem eMm43_r : tableEnergyRadius t wMm43 4 1 = (640590263179318839335044904882836072552511680624986071596962124579929905082705802283332 : ℤ) := by
  exact KsIndex.NegSignProdFastMm43.eMm43_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm43_c
#print axioms KsIndex.NegSignProd.eMm43_r
