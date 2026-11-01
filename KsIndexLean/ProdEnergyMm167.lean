module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache18688
public import KsIndexLean.AlphaLowSampleCache18944

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm167 : Finset ℤ := Finset.Ioc (2495) (2559)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm167
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm167)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (2559) then Cache18688.entries[(n - (2303)).toNat]?.getD (0, 0)
  else Cache18944.entries[(n - (2559)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm167) : (2495) < n ∧ n ≤ (2559) := by
  simpa only [wMm167, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm167) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm167) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm167) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (2559)
  · have hi : (n - (2303)).toNat < 256 := by omega
    have hm : 2 * Cache18688.mode (n - (2303)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache18688.mode]
      omega
    have hc := Cache18688.checked ⟨(n - (2303)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (2559)).toNat < 256 := by omega
    have hm : 2 * Cache18944.mode (n - (2559)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache18944.mode]
      omega
    have hc := Cache18944.checked ⟨(n - (2559)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm167) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm167) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm167_c_fast : tableEnergyNumerator t wMm167 4 1 = (2916594085784986504446949768873167861404856352565654006275346743631514562211154935393472917585128 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm167 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm167 4 1 =
      ∑ n ∈ wMm167, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm167_r_fast : tableEnergyRadius t wMm167 4 1 = (9530348317840253277564731687496620495754703576987378323534650338386402227715865916102201 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm167 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm167 4 1 =
      ∑ n ∈ wMm167, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm167

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm167_c : tableEnergyNumerator t wMm167 4 1 = (2916594085784986504446949768873167861404856352565654006275346743631514562211154935393472917585128 : ℤ) := by
  exact KsIndex.NegSignProdFastMm167.eMm167_c_fast
theorem eMm167_r : tableEnergyRadius t wMm167 4 1 = (9530348317840253277564731687496620495754703576987378323534650338386402227715865916102201 : ℤ) := by
  exact KsIndex.NegSignProdFastMm167.eMm167_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm167_c
#print axioms KsIndex.NegSignProd.eMm167_r
