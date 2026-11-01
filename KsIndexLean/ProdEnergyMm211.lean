module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache21504
public import KsIndexLean.AlphaLowSampleCache21760

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm211 : Finset ℤ := Finset.Ioc (5311) (5375)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm211
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm211)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (5375) then Cache21504.entries[(n - (5119)).toNat]?.getD (0, 0)
  else Cache21760.entries[(n - (5375)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm211) : (5311) < n ∧ n ≤ (5375) := by
  simpa only [wMm211, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm211) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm211) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm211) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (5375)
  · have hi : (n - (5119)).toNat < 256 := by omega
    have hm : 2 * Cache21504.mode (n - (5119)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache21504.mode]
      omega
    have hc := Cache21504.checked ⟨(n - (5119)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (5375)).toNat < 256 := by omega
    have hm : 2 * Cache21760.mode (n - (5375)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache21760.mode]
      omega
    have hc := Cache21760.checked ⟨(n - (5375)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm211) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm211) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm211_c_fast : tableEnergyNumerator t wMm211 4 1 = (671961670391386140535263061536009066511487608362832671926218422021166654435370048223748271743282 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm211 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm211 4 1 =
      ∑ n ∈ wMm211, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm211_r_fast : tableEnergyRadius t wMm211 4 1 = (2104608500717532877453695769924147107526506110257989658210415026891634342240656763615957 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm211 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm211 4 1 =
      ∑ n ∈ wMm211, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm211

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm211_c : tableEnergyNumerator t wMm211 4 1 = (671961670391386140535263061536009066511487608362832671926218422021166654435370048223748271743282 : ℤ) := by
  exact KsIndex.NegSignProdFastMm211.eMm211_c_fast
theorem eMm211_r : tableEnergyRadius t wMm211 4 1 = (2104608500717532877453695769924147107526506110257989658210415026891634342240656763615957 : ℤ) := by
  exact KsIndex.NegSignProdFastMm211.eMm211_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm211_c
#print axioms KsIndex.NegSignProd.eMm211_r
