module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache11008

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm46 : Finset ℤ := Finset.Ioc (-5249) (-5185)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm46

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm46)

def idx (n : ℤ) : ℕ := (n - (-5377)).toNat

lemma mem_wMm46 {n : ℤ} (hn : n ∈ wMm46) : (-5249) < n ∧ n ≤ (-5185) := by
  simpa only [wMm46, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm46) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm46 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm46) :
    2 * Cache11008.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm46 hn
  simp only [idx, Cache11008.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm46) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm46 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm46) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm46 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm46) :
    sampleNumerator (2 * n + 1) =
      (Cache11008.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache11008.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm46) :
    sampleRadius (2 * n + 1) =
      (Cache11008.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache11008.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm46_c_fast : tableEnergyNumerator t wMm46 4 1 = (67524749935065490166116038532664268072250623630952386403986644416900969565400553951492444447696 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm46 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm46 4 1 =
      ∑ n ∈ wMm46, ((6 * n + 4) ^ 2 - 4) *
        ((Cache11008.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm46_r_fast : tableEnergyRadius t wMm46 4 1 = (684106611817804357387135869950134665312655905348213525173948526493577092468788004955471 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm46 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm46 4 1 =
      ∑ n ∈ wMm46, (|((6 * n + 4) ^ 2 - 4)| * (Cache11008.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache11008.entries[idx n]?.getD (0, 0)).1| +
          (Cache11008.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm46

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm46_c : tableEnergyNumerator t wMm46 4 1 = (67524749935065490166116038532664268072250623630952386403986644416900969565400553951492444447696 : ℤ) := by
  exact KsIndex.NegSignProdFastMm46.eMm46_c_fast
theorem eMm46_r : tableEnergyRadius t wMm46 4 1 = (684106611817804357387135869950134665312655905348213525173948526493577092468788004955471 : ℤ) := by
  exact KsIndex.NegSignProdFastMm46.eMm46_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm46_c
#print axioms KsIndex.NegSignProd.eMm46_r
