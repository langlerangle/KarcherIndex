module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache16640
public import KsIndexLean.AlphaLowSampleCache16896

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm135 : Finset ℤ := Finset.Ioc (447) (511)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm135
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm135)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (511) then Cache16640.entries[(n - (255)).toNat]?.getD (0, 0)
  else Cache16896.entries[(n - (511)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm135) : (447) < n ∧ n ≤ (511) := by
  simpa only [wMm135, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm135) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm135) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm135) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (511)
  · have hi : (n - (255)).toNat < 256 := by omega
    have hm : 2 * Cache16640.mode (n - (255)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache16640.mode]
      omega
    have hc := Cache16640.checked ⟨(n - (255)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (511)).toNat < 256 := by omega
    have hm : 2 * Cache16896.mode (n - (511)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache16896.mode]
      omega
    have hc := Cache16896.checked ⟨(n - (511)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm135) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm135) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm135_c_fast : tableEnergyNumerator t wMm135 4 1 = (77417983738720581533911920501132515365715116077095761088047437982363860349665089018742989936568624 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm135 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm135 4 1 =
      ∑ n ∈ wMm135, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm135_r_fast : tableEnergyRadius t wMm135 4 1 = (277378662682049358667668985326851186625474095800959828860478545711910810725727497992638664 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm135 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm135 4 1 =
      ∑ n ∈ wMm135, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm135

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm135_c : tableEnergyNumerator t wMm135 4 1 = (77417983738720581533911920501132515365715116077095761088047437982363860349665089018742989936568624 : ℤ) := by
  exact KsIndex.NegSignProdFastMm135.eMm135_c_fast
theorem eMm135_r : tableEnergyRadius t wMm135 4 1 = (277378662682049358667668985326851186625474095800959828860478545711910810725727497992638664 : ℤ) := by
  exact KsIndex.NegSignProdFastMm135.eMm135_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm135_c
#print axioms KsIndex.NegSignProd.eMm135_r
