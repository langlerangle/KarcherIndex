module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache9216

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm17 : Finset ℤ := Finset.Ioc (-7105) (-7041)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm17

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm17)

def idx (n : ℤ) : ℕ := (n - (-7169)).toNat

lemma mem_wMm17 {n : ℤ} (hn : n ∈ wMm17) : (-7105) < n ∧ n ≤ (-7041) := by
  simpa only [wMm17, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm17) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm17 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm17) :
    2 * Cache9216.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm17 hn
  simp only [idx, Cache9216.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm17) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm17 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm17) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm17 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm17) :
    sampleNumerator (2 * n + 1) =
      (Cache9216.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache9216.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm17) :
    sampleRadius (2 * n + 1) =
      (Cache9216.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache9216.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm17_c_fast : tableEnergyNumerator t wMm17 4 1 = (41798920888698452634395125657681121181169301660659873981557225047706525600892238844016918126760 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm17 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm17 4 1 =
      ∑ n ∈ wMm17, ((6 * n + 4) ^ 2 - 4) *
        ((Cache9216.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm17_r_fast : tableEnergyRadius t wMm17 4 1 = (392722048540804889044637875505212394775991961599049098366285844395120632017348273938729 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm17 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm17 4 1 =
      ∑ n ∈ wMm17, (|((6 * n + 4) ^ 2 - 4)| * (Cache9216.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache9216.entries[idx n]?.getD (0, 0)).1| +
          (Cache9216.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm17

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm17_c : tableEnergyNumerator t wMm17 4 1 = (41798920888698452634395125657681121181169301660659873981557225047706525600892238844016918126760 : ℤ) := by
  exact KsIndex.NegSignProdFastMm17.eMm17_c_fast
theorem eMm17_r : tableEnergyRadius t wMm17 4 1 = (392722048540804889044637875505212394775991961599049098366285844395120632017348273938729 : ℤ) := by
  exact KsIndex.NegSignProdFastMm17.eMm17_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm17_c
#print axioms KsIndex.NegSignProd.eMm17_r
