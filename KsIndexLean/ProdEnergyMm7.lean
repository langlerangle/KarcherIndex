module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache8448
public import KsIndexLean.AlphaLowSampleCache8704

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm7 : Finset ℤ := Finset.Ioc (-7745) (-7681)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm7
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm7)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-7681) then Cache8448.entries[(n - (-7937)).toNat]?.getD (0, 0)
  else Cache8704.entries[(n - (-7681)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm7) : (-7745) < n ∧ n ≤ (-7681) := by
  simpa only [wMm7, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm7) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm7) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm7) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-7681)
  · have hi : (n - (-7937)).toNat < 256 := by omega
    have hm : 2 * Cache8448.mode (n - (-7937)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache8448.mode]
      omega
    have hc := Cache8448.checked ⟨(n - (-7937)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-7681)).toNat < 256 := by omega
    have hm : 2 * Cache8704.mode (n - (-7681)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache8704.mode]
      omega
    have hc := Cache8704.checked ⟨(n - (-7681)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm7) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm7) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm7_c_fast : tableEnergyNumerator t wMm7 4 1 = (36417400427476884675897754465778189421570762743399695526325436039703368052121284318813882155923 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm7 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm7 4 1 =
      ∑ n ∈ wMm7, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm7_r_fast : tableEnergyRadius t wMm7 4 1 = (335138249835430355806060260219444092360517351183519242970186934786851979982380914626936 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm7 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm7 4 1 =
      ∑ n ∈ wMm7, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm7

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm7_c : tableEnergyNumerator t wMm7 4 1 = (36417400427476884675897754465778189421570762743399695526325436039703368052121284318813882155923 : ℤ) := by
  exact KsIndex.NegSignProdFastMm7.eMm7_c_fast
theorem eMm7_r : tableEnergyRadius t wMm7 4 1 = (335138249835430355806060260219444092360517351183519242970186934786851979982380914626936 : ℤ) := by
  exact KsIndex.NegSignProdFastMm7.eMm7_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm7_c
#print axioms KsIndex.NegSignProd.eMm7_r
