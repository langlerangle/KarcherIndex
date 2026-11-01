module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache21248

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm205 : Finset ℤ := Finset.Ioc (4927) (4991)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm205

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm205)

def idx (n : ℤ) : ℕ := (n - (4863)).toNat

lemma mem_wMm205 {n : ℤ} (hn : n ∈ wMm205) : (4927) < n ∧ n ≤ (4991) := by
  simpa only [wMm205, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm205) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm205 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm205) :
    2 * Cache21248.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm205 hn
  simp only [idx, Cache21248.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm205) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm205 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm205) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm205 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm205) :
    sampleNumerator (2 * n + 1) =
      (Cache21248.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache21248.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm205) :
    sampleRadius (2 * n + 1) =
      (Cache21248.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache21248.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm205_c_fast : tableEnergyNumerator t wMm205 4 1 = (777608964691616070812074313157581140693710207340441979984905201377284959662720886161212276793254 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm205 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm205 4 1 =
      ∑ n ∈ wMm205, ((6 * n + 4) ^ 2 - 4) *
        ((Cache21248.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm205_r_fast : tableEnergyRadius t wMm205 4 1 = (2445857344215047234548671045017922767185526235403606799459428179487009348549533984148351 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm205 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm205 4 1 =
      ∑ n ∈ wMm205, (|((6 * n + 4) ^ 2 - 4)| * (Cache21248.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache21248.entries[idx n]?.getD (0, 0)).1| +
          (Cache21248.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm205

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm205_c : tableEnergyNumerator t wMm205 4 1 = (777608964691616070812074313157581140693710207340441979984905201377284959662720886161212276793254 : ℤ) := by
  exact KsIndex.NegSignProdFastMm205.eMm205_c_fast
theorem eMm205_r : tableEnergyRadius t wMm205 4 1 = (2445857344215047234548671045017922767185526235403606799459428179487009348549533984148351 : ℤ) := by
  exact KsIndex.NegSignProdFastMm205.eMm205_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm205_c
#print axioms KsIndex.NegSignProd.eMm205_r
