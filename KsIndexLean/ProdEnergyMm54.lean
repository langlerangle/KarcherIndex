module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache11520

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm54 : Finset ℤ := Finset.Ioc (-4737) (-4673)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm54

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm54)

def idx (n : ℤ) : ℕ := (n - (-4865)).toNat

lemma mem_wMm54 {n : ℤ} (hn : n ∈ wMm54) : (-4737) < n ∧ n ≤ (-4673) := by
  simpa only [wMm54, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm54) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm54 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm54) :
    2 * Cache11520.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm54 hn
  simp only [idx, Cache11520.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm54) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm54 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm54) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm54 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm54) :
    sampleNumerator (2 * n + 1) =
      (Cache11520.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache11520.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm54) :
    sampleRadius (2 * n + 1) =
      (Cache11520.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache11520.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm54_c_fast : tableEnergyNumerator t wMm54 4 1 = (79321652456437447933941430725668608833743559625185670317155039537384969060889665954952690784807 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm54 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm54 4 1 =
      ∑ n ∈ wMm54, ((6 * n + 4) ^ 2 - 4) *
        ((Cache11520.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm54_r_fast : tableEnergyRadius t wMm54 4 1 = (825237921509435480244720698813508843737947817290685466644007084508366142272047826584540 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm54 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm54 4 1 =
      ∑ n ∈ wMm54, (|((6 * n + 4) ^ 2 - 4)| * (Cache11520.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache11520.entries[idx n]?.getD (0, 0)).1| +
          (Cache11520.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm54

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm54_c : tableEnergyNumerator t wMm54 4 1 = (79321652456437447933941430725668608833743559625185670317155039537384969060889665954952690784807 : ℤ) := by
  exact KsIndex.NegSignProdFastMm54.eMm54_c_fast
theorem eMm54_r : tableEnergyRadius t wMm54 4 1 = (825237921509435480244720698813508843737947817290685466644007084508366142272047826584540 : ℤ) := by
  exact KsIndex.NegSignProdFastMm54.eMm54_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm54_c
#print axioms KsIndex.NegSignProd.eMm54_r
