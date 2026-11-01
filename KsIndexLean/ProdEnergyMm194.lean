module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache20480

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm194 : Finset ℤ := Finset.Ioc (4223) (4287)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm194

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm194)

def idx (n : ℤ) : ℕ := (n - (4095)).toNat

lemma mem_wMm194 {n : ℤ} (hn : n ∈ wMm194) : (4223) < n ∧ n ≤ (4287) := by
  simpa only [wMm194, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm194) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm194 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm194) :
    2 * Cache20480.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm194 hn
  simp only [idx, Cache20480.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm194) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm194 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm194) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm194 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm194) :
    sampleNumerator (2 * n + 1) =
      (Cache20480.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache20480.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm194) :
    sampleRadius (2 * n + 1) =
      (Cache20480.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache20480.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm194_c_fast : tableEnergyNumerator t wMm194 4 1 = (1049561283901269409176110061046958314750302282111506801991681042492014890175151430015782483141808 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm194 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm194 4 1 =
      ∑ n ∈ wMm194, ((6 * n + 4) ^ 2 - 4) *
        ((Cache20480.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm194_r_fast : tableEnergyRadius t wMm194 4 1 = (3330082058343743203617339806962888363111517872796467138960482587482474589182947477009185 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm194 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm194 4 1 =
      ∑ n ∈ wMm194, (|((6 * n + 4) ^ 2 - 4)| * (Cache20480.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache20480.entries[idx n]?.getD (0, 0)).1| +
          (Cache20480.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm194

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm194_c : tableEnergyNumerator t wMm194 4 1 = (1049561283901269409176110061046958314750302282111506801991681042492014890175151430015782483141808 : ℤ) := by
  exact KsIndex.NegSignProdFastMm194.eMm194_c_fast
theorem eMm194_r : tableEnergyRadius t wMm194 4 1 = (3330082058343743203617339806962888363111517872796467138960482587482474589182947477009185 : ℤ) := by
  exact KsIndex.NegSignProdFastMm194.eMm194_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm194_c
#print axioms KsIndex.NegSignProd.eMm194_r
