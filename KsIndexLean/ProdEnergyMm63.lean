module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache12032
public import KsIndexLean.AlphaLowSampleCache12288

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm63 : Finset ℤ := Finset.Ioc (-4161) (-4097)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm63
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm63)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-4097) then Cache12032.entries[(n - (-4353)).toNat]?.getD (0, 0)
  else Cache12288.entries[(n - (-4097)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm63) : (-4161) < n ∧ n ≤ (-4097) := by
  simpa only [wMm63, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm63) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm63) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm63) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-4097)
  · have hi : (n - (-4353)).toNat < 256 := by omega
    have hm : 2 * Cache12032.mode (n - (-4353)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache12032.mode]
      omega
    have hc := Cache12032.checked ⟨(n - (-4353)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-4097)).toNat < 256 := by omega
    have hm : 2 * Cache12288.mode (n - (-4097)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache12288.mode]
      omega
    have hc := Cache12288.checked ⟨(n - (-4097)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm63) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm63) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm63_c_fast : tableEnergyNumerator t wMm63 4 1 = (97095243231237042690150772668408364984187534533397279385069661902983780559726068740360567204343 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm63 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm63 4 1 =
      ∑ n ∈ wMm63, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm63_r_fast : tableEnergyRadius t wMm63 4 1 = (1045396594573649038944419366577986870929933256428244644694010321492083180540007634944249 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm63 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm63 4 1 =
      ∑ n ∈ wMm63, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm63

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm63_c : tableEnergyNumerator t wMm63 4 1 = (97095243231237042690150772668408364984187534533397279385069661902983780559726068740360567204343 : ℤ) := by
  exact KsIndex.NegSignProdFastMm63.eMm63_c_fast
theorem eMm63_r : tableEnergyRadius t wMm63 4 1 = (1045396594573649038944419366577986870929933256428244644694010321492083180540007634944249 : ℤ) := by
  exact KsIndex.NegSignProdFastMm63.eMm63_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm63_c
#print axioms KsIndex.NegSignProd.eMm63_r
