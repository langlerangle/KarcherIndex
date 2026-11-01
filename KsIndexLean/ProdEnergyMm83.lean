module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache13312
public import KsIndexLean.AlphaLowSampleCache13568

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm83 : Finset ℤ := Finset.Ioc (-2881) (-2817)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm83
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm83)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-2817) then Cache13312.entries[(n - (-3073)).toNat]?.getD (0, 0)
  else Cache13568.entries[(n - (-2817)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm83) : (-2881) < n ∧ n ≤ (-2817) := by
  simpa only [wMm83, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm83) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm83) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm83) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-2817)
  · have hi : (n - (-3073)).toNat < 256 := by omega
    have hm : 2 * Cache13312.mode (n - (-3073)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache13312.mode]
      omega
    have hc := Cache13312.checked ⟨(n - (-3073)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-2817)).toNat < 256 := by omega
    have hm : 2 * Cache13568.mode (n - (-2817)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache13568.mode]
      omega
    have hc := Cache13568.checked ⟨(n - (-2817)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm83) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm83) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm83_c_fast : tableEnergyNumerator t wMm83 4 1 = (170877714841749745226864357298979105436900854465692780975976827486089458498288508074713693948987 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm83 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm83 4 1 =
      ∑ n ∈ wMm83, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm83_r_fast : tableEnergyRadius t wMm83 4 1 = (2038191922728926821895895379113227001599386595429659442528029921270340554629091782748061 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm83 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm83 4 1 =
      ∑ n ∈ wMm83, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm83

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm83_c : tableEnergyNumerator t wMm83 4 1 = (170877714841749745226864357298979105436900854465692780975976827486089458498288508074713693948987 : ℤ) := by
  exact KsIndex.NegSignProdFastMm83.eMm83_c_fast
theorem eMm83_r : tableEnergyRadius t wMm83 4 1 = (2038191922728926821895895379113227001599386595429659442528029921270340554629091782748061 : ℤ) := by
  exact KsIndex.NegSignProdFastMm83.eMm83_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm83_c
#print axioms KsIndex.NegSignProd.eMm83_r
