module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache20480
public import KsIndexLean.AlphaLowSampleCache20736

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm195 : Finset ℤ := Finset.Ioc (4287) (4351)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm195
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm195)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (4351) then Cache20480.entries[(n - (4095)).toNat]?.getD (0, 0)
  else Cache20736.entries[(n - (4351)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm195) : (4287) < n ∧ n ≤ (4351) := by
  simpa only [wMm195, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm195) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm195) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm195) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (4351)
  · have hi : (n - (4095)).toNat < 256 := by omega
    have hm : 2 * Cache20480.mode (n - (4095)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache20480.mode]
      omega
    have hc := Cache20480.checked ⟨(n - (4095)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (4351)).toNat < 256 := by omega
    have hm : 2 * Cache20736.mode (n - (4351)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache20736.mode]
      omega
    have hc := Cache20736.checked ⟨(n - (4351)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm195) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm195) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm195_c_fast : tableEnergyNumerator t wMm195 4 1 = (1019305479495723131125925587825634316349582514420668968838461880578002157222607827877556998065632 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm195 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm195 4 1 =
      ∑ n ∈ wMm195, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm195_r_fast : tableEnergyRadius t wMm195 4 1 = (3231346761302820420133229423913361033598618252954437916097031425601088112256394060514958 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm195 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm195 4 1 =
      ∑ n ∈ wMm195, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm195

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm195_c : tableEnergyNumerator t wMm195 4 1 = (1019305479495723131125925587825634316349582514420668968838461880578002157222607827877556998065632 : ℤ) := by
  exact KsIndex.NegSignProdFastMm195.eMm195_c_fast
theorem eMm195_r : tableEnergyRadius t wMm195 4 1 = (3231346761302820420133229423913361033598618252954437916097031425601088112256394060514958 : ℤ) := by
  exact KsIndex.NegSignProdFastMm195.eMm195_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm195_c
#print axioms KsIndex.NegSignProd.eMm195_r
