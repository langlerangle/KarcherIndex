module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache8704
public import KsIndexLean.AlphaLowSampleCache8960

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm11 : Finset ℤ := Finset.Ioc (-7489) (-7425)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm11
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm11)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-7425) then Cache8704.entries[(n - (-7681)).toNat]?.getD (0, 0)
  else Cache8960.entries[(n - (-7425)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm11) : (-7489) < n ∧ n ≤ (-7425) := by
  simpa only [wMm11, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm11) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm11) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm11) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-7425)
  · have hi : (n - (-7681)).toNat < 256 := by omega
    have hm : 2 * Cache8704.mode (n - (-7681)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache8704.mode]
      omega
    have hc := Cache8704.checked ⟨(n - (-7681)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-7425)).toNat < 256 := by omega
    have hm : 2 * Cache8960.mode (n - (-7425)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache8960.mode]
      omega
    have hc := Cache8960.checked ⟨(n - (-7425)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm11) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm11) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm11_c_fast : tableEnergyNumerator t wMm11 4 1 = (38429234605472215730710220276913441682289806723314269948766731768826484812467950886271389181286 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm11 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm11 4 1 =
      ∑ n ∈ wMm11, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm11_r_fast : tableEnergyRadius t wMm11 4 1 = (356508641106395002043412954112481049185721404821091074428620684255250555222809778020779 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm11 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm11 4 1 =
      ∑ n ∈ wMm11, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm11

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm11_c : tableEnergyNumerator t wMm11 4 1 = (38429234605472215730710220276913441682289806723314269948766731768826484812467950886271389181286 : ℤ) := by
  exact KsIndex.NegSignProdFastMm11.eMm11_c_fast
theorem eMm11_r : tableEnergyRadius t wMm11 4 1 = (356508641106395002043412954112481049185721404821091074428620684255250555222809778020779 : ℤ) := by
  exact KsIndex.NegSignProdFastMm11.eMm11_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm11_c
#print axioms KsIndex.NegSignProd.eMm11_r
