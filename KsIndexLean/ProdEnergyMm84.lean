module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache13568

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm84 : Finset ℤ := Finset.Ioc (-2817) (-2753)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm84

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm84)

def idx (n : ℤ) : ℕ := (n - (-2817)).toNat

lemma mem_wMm84 {n : ℤ} (hn : n ∈ wMm84) : (-2817) < n ∧ n ≤ (-2753) := by
  simpa only [wMm84, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm84) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm84 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm84) :
    2 * Cache13568.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm84 hn
  simp only [idx, Cache13568.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm84) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm84 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm84) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm84 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm84) :
    sampleNumerator (2 * n + 1) =
      (Cache13568.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache13568.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm84) :
    sampleRadius (2 * n + 1) =
      (Cache13568.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache13568.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm84_c_fast : tableEnergyNumerator t wMm84 4 1 = (176810177566236056341701512383095289886410668124853007989009622887653109694707565053497866203756 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm84 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm84 4 1 =
      ∑ n ∈ wMm84, ((6 * n + 4) ^ 2 - 4) *
        ((Cache13568.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm84_r_fast : tableEnergyRadius t wMm84 4 1 = (2122765017767861904231101930832439507205349708457707233241122486369725210978871403827794 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm84 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm84 4 1 =
      ∑ n ∈ wMm84, (|((6 * n + 4) ^ 2 - 4)| * (Cache13568.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache13568.entries[idx n]?.getD (0, 0)).1| +
          (Cache13568.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm84

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm84_c : tableEnergyNumerator t wMm84 4 1 = (176810177566236056341701512383095289886410668124853007989009622887653109694707565053497866203756 : ℤ) := by
  exact KsIndex.NegSignProdFastMm84.eMm84_c_fast
theorem eMm84_r : tableEnergyRadius t wMm84 4 1 = (2122765017767861904231101930832439507205349708457707233241122486369725210978871403827794 : ℤ) := by
  exact KsIndex.NegSignProdFastMm84.eMm84_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm84_c
#print axioms KsIndex.NegSignProd.eMm84_r
