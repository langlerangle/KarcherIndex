module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache18176
public import KsIndexLean.AlphaLowSampleCache18432

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm159 : Finset ℤ := Finset.Ioc (1983) (2047)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm159
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm159)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (2047) then Cache18176.entries[(n - (1791)).toNat]?.getD (0, 0)
  else Cache18432.entries[(n - (2047)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm159) : (1983) < n ∧ n ≤ (2047) := by
  simpa only [wMm159, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm159) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm159) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm159) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (2047)
  · have hi : (n - (1791)).toNat < 256 := by omega
    have hm : 2 * Cache18176.mode (n - (1791)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache18176.mode]
      omega
    have hc := Cache18176.checked ⟨(n - (1791)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (2047)).toNat < 256 := by omega
    have hm : 2 * Cache18432.mode (n - (2047)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache18432.mode]
      omega
    have hc := Cache18432.checked ⟨(n - (2047)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm159) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm159) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm159_c_fast : tableEnergyNumerator t wMm159 4 1 = (4550369129957535831088306330590010757413418164681117802578062574924431068775734543274966992515349 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm159 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm159 4 1 =
      ∑ n ∈ wMm159, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm159_r_fast : tableEnergyRadius t wMm159 4 1 = (15059087216794376710747331486933589568399718903665878300249929762903864246722682554810397 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm159 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm159 4 1 =
      ∑ n ∈ wMm159, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm159

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm159_c : tableEnergyNumerator t wMm159 4 1 = (4550369129957535831088306330590010757413418164681117802578062574924431068775734543274966992515349 : ℤ) := by
  exact KsIndex.NegSignProdFastMm159.eMm159_c_fast
theorem eMm159_r : tableEnergyRadius t wMm159 4 1 = (15059087216794376710747331486933589568399718903665878300249929762903864246722682554810397 : ℤ) := by
  exact KsIndex.NegSignProdFastMm159.eMm159_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm159_c
#print axioms KsIndex.NegSignProd.eMm159_r
