module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache10496
public import KsIndexLean.AlphaLowSampleCache10752

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm39 : Finset ℤ := Finset.Ioc (-5697) (-5633)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm39
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm39)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-5633) then Cache10496.entries[(n - (-5889)).toNat]?.getD (0, 0)
  else Cache10752.entries[(n - (-5633)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm39) : (-5697) < n ∧ n ≤ (-5633) := by
  simpa only [wMm39, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm39) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm39) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm39) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-5633)
  · have hi : (n - (-5889)).toNat < 256 := by omega
    have hm : 2 * Cache10496.mode (n - (-5889)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache10496.mode]
      omega
    have hc := Cache10496.checked ⟨(n - (-5889)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-5633)).toNat < 256 := by omega
    have hm : 2 * Cache10752.mode (n - (-5633)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache10752.mode]
      omega
    have hc := Cache10752.checked ⟨(n - (-5633)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm39) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm39) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm39_c_fast : tableEnergyNumerator t wMm39 4 1 = (59347794163963468206902945077004440177412702861854531265925379656723746166605211100140089065479 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm39 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm39 4 1 =
      ∑ n ∈ wMm39, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm39_r_fast : tableEnergyRadius t wMm39 4 1 = (588880874668970018435334202228883850127107667741376274671527140543725800472756066585896 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm39 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm39 4 1 =
      ∑ n ∈ wMm39, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm39

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm39_c : tableEnergyNumerator t wMm39 4 1 = (59347794163963468206902945077004440177412702861854531265925379656723746166605211100140089065479 : ℤ) := by
  exact KsIndex.NegSignProdFastMm39.eMm39_c_fast
theorem eMm39_r : tableEnergyRadius t wMm39 4 1 = (588880874668970018435334202228883850127107667741376274671527140543725800472756066585896 : ℤ) := by
  exact KsIndex.NegSignProdFastMm39.eMm39_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm39_c
#print axioms KsIndex.NegSignProd.eMm39_r
