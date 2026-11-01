module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache23296
public import KsIndexLean.AlphaLowSampleCache23552

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm239 : Finset ℤ := Finset.Ioc (7103) (7167)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm239
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm239)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (7167) then Cache23296.entries[(n - (6911)).toNat]?.getD (0, 0)
  else Cache23552.entries[(n - (7167)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm239) : (7103) < n ∧ n ≤ (7167) := by
  simpa only [wMm239, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm239) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm239) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm239) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (7167)
  · have hi : (n - (6911)).toNat < 256 := by omega
    have hm : 2 * Cache23296.mode (n - (6911)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache23296.mode]
      omega
    have hc := Cache23296.checked ⟨(n - (6911)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (7167)).toNat < 256 := by omega
    have hm : 2 * Cache23552.mode (n - (7167)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache23552.mode]
      omega
    have hc := Cache23552.checked ⟨(n - (7167)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm239) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm239) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm239_c_fast : tableEnergyNumerator t wMm239 4 1 = (381595465181470665265293487056751644081381024354046548203742272478159361819526658006790740538284 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm239 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm239 4 1 =
      ∑ n ∈ wMm239, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm239_r_fast : tableEnergyRadius t wMm239 4 1 = (1175615772697132597421532519584695205335269171243520070227400918639140238032435650032271 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm239 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm239 4 1 =
      ∑ n ∈ wMm239, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm239

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm239_c : tableEnergyNumerator t wMm239 4 1 = (381595465181470665265293487056751644081381024354046548203742272478159361819526658006790740538284 : ℤ) := by
  exact KsIndex.NegSignProdFastMm239.eMm239_c_fast
theorem eMm239_r : tableEnergyRadius t wMm239 4 1 = (1175615772697132597421532519584695205335269171243520070227400918639140238032435650032271 : ℤ) := by
  exact KsIndex.NegSignProdFastMm239.eMm239_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm239_c
#print axioms KsIndex.NegSignProd.eMm239_r
