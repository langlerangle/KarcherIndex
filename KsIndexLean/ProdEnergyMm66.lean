module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache12288

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm66 : Finset ℤ := Finset.Ioc (-3969) (-3905)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm66

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm66)

def idx (n : ℤ) : ℕ := (n - (-4097)).toNat

lemma mem_wMm66 {n : ℤ} (hn : n ∈ wMm66) : (-3969) < n ∧ n ≤ (-3905) := by
  simpa only [wMm66, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm66) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm66 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm66) :
    2 * Cache12288.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm66 hn
  simp only [idx, Cache12288.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm66) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm66 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm66) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm66 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm66) :
    sampleNumerator (2 * n + 1) =
      (Cache12288.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache12288.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm66) :
    sampleRadius (2 * n + 1) =
      (Cache12288.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache12288.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm66_c_fast : tableEnergyNumerator t wMm66 4 1 = (104481726988729025641425958772872164657942235048632327546098824269437652743349133238625932926828 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm66 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm66 4 1 =
      ∑ n ∈ wMm66, ((6 * n + 4) ^ 2 - 4) *
        ((Cache12288.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm66_r_fast : tableEnergyRadius t wMm66 4 1 = (1139326596254069931235184920193791958987376360884719771831493363116715495467388840443166 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm66 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm66 4 1 =
      ∑ n ∈ wMm66, (|((6 * n + 4) ^ 2 - 4)| * (Cache12288.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache12288.entries[idx n]?.getD (0, 0)).1| +
          (Cache12288.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm66

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm66_c : tableEnergyNumerator t wMm66 4 1 = (104481726988729025641425958772872164657942235048632327546098824269437652743349133238625932926828 : ℤ) := by
  exact KsIndex.NegSignProdFastMm66.eMm66_c_fast
theorem eMm66_r : tableEnergyRadius t wMm66 4 1 = (1139326596254069931235184920193791958987376360884719771831493363116715495467388840443166 : ℤ) := by
  exact KsIndex.NegSignProdFastMm66.eMm66_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm66_c
#print axioms KsIndex.NegSignProd.eMm66_r
