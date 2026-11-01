module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache23552
public import KsIndexLean.AlphaLowSampleCache23808

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm243 : Finset ℤ := Finset.Ioc (7359) (7423)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm243
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm243)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (7423) then Cache23552.entries[(n - (7167)).toNat]?.getD (0, 0)
  else Cache23808.entries[(n - (7423)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm243) : (7359) < n ∧ n ≤ (7423) := by
  simpa only [wMm243, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm243) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm243) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm243) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (7423)
  · have hi : (n - (7167)).toNat < 256 := by omega
    have hm : 2 * Cache23552.mode (n - (7167)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache23552.mode]
      omega
    have hc := Cache23552.checked ⟨(n - (7167)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (7423)).toNat < 256 := by omega
    have hm : 2 * Cache23808.mode (n - (7423)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache23808.mode]
      omega
    have hc := Cache23808.checked ⟨(n - (7423)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm243) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm243) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm243_c_fast : tableEnergyNumerator t wMm243 4 1 = (356181931824173403389874572563349659544407777821138485305831574530012931672457824363949274344941 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm243 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm243 4 1 =
      ∑ n ∈ wMm243, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm243_r_fast : tableEnergyRadius t wMm243 4 1 = (1095113357227272965345097966413593659619516484394692731288598213384144621659297536285260 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm243 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm243 4 1 =
      ∑ n ∈ wMm243, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm243

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm243_c : tableEnergyNumerator t wMm243 4 1 = (356181931824173403389874572563349659544407777821138485305831574530012931672457824363949274344941 : ℤ) := by
  exact KsIndex.NegSignProdFastMm243.eMm243_c_fast
theorem eMm243_r : tableEnergyRadius t wMm243 4 1 = (1095113357227272965345097966413593659619516484394692731288598213384144621659297536285260 : ℤ) := by
  exact KsIndex.NegSignProdFastMm243.eMm243_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm243_c
#print axioms KsIndex.NegSignProd.eMm243_r
