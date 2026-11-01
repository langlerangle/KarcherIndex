module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache20736
public import KsIndexLean.AlphaLowSampleCache20992

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm199 : Finset ℤ := Finset.Ioc (4543) (4607)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm199
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm199)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (4607) then Cache20736.entries[(n - (4351)).toNat]?.getD (0, 0)
  else Cache20992.entries[(n - (4607)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm199) : (4543) < n ∧ n ≤ (4607) := by
  simpa only [wMm199, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm199) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm199) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm199) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (4607)
  · have hi : (n - (4351)).toNat < 256 := by omega
    have hm : 2 * Cache20736.mode (n - (4351)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache20736.mode]
      omega
    have hc := Cache20736.checked ⟨(n - (4351)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (4607)).toNat < 256 := by omega
    have hm : 2 * Cache20992.mode (n - (4607)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache20992.mode]
      omega
    have hc := Cache20992.checked ⟨(n - (4607)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm199) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm199) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm199_c_fast : tableEnergyNumerator t wMm199 4 1 = (910570247226415667632309019236573389511895023642215615933008092169715662130410798981060540244023 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm199 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm199 4 1 =
      ∑ n ∈ wMm199, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm199_r_fast : tableEnergyRadius t wMm199 4 1 = (2877217953604399591201548854469503846596932061397251683067337518439223922724751507520000 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm199 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm199 4 1 =
      ∑ n ∈ wMm199, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm199

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm199_c : tableEnergyNumerator t wMm199 4 1 = (910570247226415667632309019236573389511895023642215615933008092169715662130410798981060540244023 : ℤ) := by
  exact KsIndex.NegSignProdFastMm199.eMm199_c_fast
theorem eMm199_r : tableEnergyRadius t wMm199 4 1 = (2877217953604399591201548854469503846596932061397251683067337518439223922724751507520000 : ℤ) := by
  exact KsIndex.NegSignProdFastMm199.eMm199_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm199_c
#print axioms KsIndex.NegSignProd.eMm199_r
