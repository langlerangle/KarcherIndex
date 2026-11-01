module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache12544
public import KsIndexLean.AlphaLowSampleCache12800

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm71 : Finset ℤ := Finset.Ioc (-3649) (-3585)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm71
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm71)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-3585) then Cache12544.entries[(n - (-3841)).toNat]?.getD (0, 0)
  else Cache12800.entries[(n - (-3585)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm71) : (-3649) < n ∧ n ≤ (-3585) := by
  simpa only [wMm71, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm71) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm71) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm71) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-3585)
  · have hi : (n - (-3841)).toNat < 256 := by omega
    have hm : 2 * Cache12544.mode (n - (-3841)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache12544.mode]
      omega
    have hc := Cache12544.checked ⟨(n - (-3841)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-3585)).toNat < 256 := by omega
    have hm : 2 * Cache12800.mode (n - (-3585)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache12800.mode]
      omega
    have hc := Cache12800.checked ⟨(n - (-3585)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm71) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm71) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm71_c_fast : tableEnergyNumerator t wMm71 4 1 = (118984979383400011215409445900517470408992943157404197637181607737469815382197956354234264952200 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm71 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm71 4 1 =
      ∑ n ∈ wMm71, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm71_r_fast : tableEnergyRadius t wMm71 4 1 = (1327591470143389115559759942890934219276699159589386506520416433374566226673671542280103 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm71 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm71 4 1 =
      ∑ n ∈ wMm71, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm71

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm71_c : tableEnergyNumerator t wMm71 4 1 = (118984979383400011215409445900517470408992943157404197637181607737469815382197956354234264952200 : ℤ) := by
  exact KsIndex.NegSignProdFastMm71.eMm71_c_fast
theorem eMm71_r : tableEnergyRadius t wMm71 4 1 = (1327591470143389115559759942890934219276699159589386506520416433374566226673671542280103 : ℤ) := by
  exact KsIndex.NegSignProdFastMm71.eMm71_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm71_c
#print axioms KsIndex.NegSignProd.eMm71_r
