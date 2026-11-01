module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache18944
public import KsIndexLean.AlphaLowSampleCache19200

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm171 : Finset ℤ := Finset.Ioc (2751) (2815)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm171
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm171)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (2815) then Cache18944.entries[(n - (2559)).toNat]?.getD (0, 0)
  else Cache19200.entries[(n - (2815)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm171) : (2751) < n ∧ n ≤ (2815) := by
  simpa only [wMm171, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm171) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm171) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm171) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (2815)
  · have hi : (n - (2559)).toNat < 256 := by omega
    have hm : 2 * Cache18944.mode (n - (2559)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache18944.mode]
      omega
    have hc := Cache18944.checked ⟨(n - (2559)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (2815)).toNat < 256 := by omega
    have hm : 2 * Cache19200.mode (n - (2815)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache19200.mode]
      omega
    have hc := Cache19200.checked ⟨(n - (2815)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm171) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm171) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm171_c_fast : tableEnergyNumerator t wMm171 4 1 = (2413253832105008715338987100636121234480426931826430827956906040066968746436003114307958078681752 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm171 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm171 4 1 =
      ∑ n ∈ wMm171, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm171_r_fast : tableEnergyRadius t wMm171 4 1 = (7842897839642215901379662765228741781321956761872564187607447310445504408224498048175542 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm171 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm171 4 1 =
      ∑ n ∈ wMm171, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm171

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm171_c : tableEnergyNumerator t wMm171 4 1 = (2413253832105008715338987100636121234480426931826430827956906040066968746436003114307958078681752 : ℤ) := by
  exact KsIndex.NegSignProdFastMm171.eMm171_c_fast
theorem eMm171_r : tableEnergyRadius t wMm171 4 1 = (7842897839642215901379662765228741781321956761872564187607447310445504408224498048175542 : ℤ) := by
  exact KsIndex.NegSignProdFastMm171.eMm171_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm171_c
#print axioms KsIndex.NegSignProd.eMm171_r
