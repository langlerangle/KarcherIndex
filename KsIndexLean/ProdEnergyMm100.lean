module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache14592

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm100 : Finset ℤ := Finset.Ioc (-1793) (-1729)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm100

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm100)

def idx (n : ℤ) : ℕ := (n - (-1793)).toNat

lemma mem_wMm100 {n : ℤ} (hn : n ∈ wMm100) : (-1793) < n ∧ n ≤ (-1729) := by
  simpa only [wMm100, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm100) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm100 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm100) :
    2 * Cache14592.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm100 hn
  simp only [idx, Cache14592.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm100) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm100 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm100) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm100 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm100) :
    sampleNumerator (2 * n + 1) =
      (Cache14592.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache14592.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm100) :
    sampleRadius (2 * n + 1) =
      (Cache14592.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache14592.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm100_c_fast : tableEnergyNumerator t wMm100 4 1 = (347205497480433163357777624859890424558111086534574704600787164094733074095696311522211713613349 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm100 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm100 4 1 =
      ∑ n ∈ wMm100, ((6 * n + 4) ^ 2 - 4) *
        ((Cache14592.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm100_r_fast : tableEnergyRadius t wMm100 4 1 = (4789969049400365810756611087823282147532492008517244239146225799724243776412680729507880 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm100 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm100 4 1 =
      ∑ n ∈ wMm100, (|((6 * n + 4) ^ 2 - 4)| * (Cache14592.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache14592.entries[idx n]?.getD (0, 0)).1| +
          (Cache14592.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm100

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm100_c : tableEnergyNumerator t wMm100 4 1 = (347205497480433163357777624859890424558111086534574704600787164094733074095696311522211713613349 : ℤ) := by
  exact KsIndex.NegSignProdFastMm100.eMm100_c_fast
theorem eMm100_r : tableEnergyRadius t wMm100 4 1 = (4789969049400365810756611087823282147532492008517244239146225799724243776412680729507880 : ℤ) := by
  exact KsIndex.NegSignProdFastMm100.eMm100_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm100_c
#print axioms KsIndex.NegSignProd.eMm100_r
