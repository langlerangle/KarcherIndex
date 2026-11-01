module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache14592

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm102 : Finset ℤ := Finset.Ioc (-1665) (-1601)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm102

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm102)

def idx (n : ℤ) : ℕ := (n - (-1793)).toNat

lemma mem_wMm102 {n : ℤ} (hn : n ∈ wMm102) : (-1665) < n ∧ n ≤ (-1601) := by
  simpa only [wMm102, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm102) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm102 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm102) :
    2 * Cache14592.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm102 hn
  simp only [idx, Cache14592.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm102) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm102 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm102) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm102 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm102) :
    sampleNumerator (2 * n + 1) =
      (Cache14592.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache14592.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm102) :
    sampleRadius (2 * n + 1) =
      (Cache14592.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache14592.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm102_c_fast : tableEnergyNumerator t wMm102 4 1 = (386937387304771876108871528333368785167134505769845773166592102187365389429205347556042167776492 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm102 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm102 4 1 =
      ∑ n ∈ wMm102, ((6 * n + 4) ^ 2 - 4) *
        ((Cache14592.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm102_r_fast : tableEnergyRadius t wMm102 4 1 = (5469617405306780614847703006544718092679377064740409656518032254977748885528880000758965 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm102 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm102 4 1 =
      ∑ n ∈ wMm102, (|((6 * n + 4) ^ 2 - 4)| * (Cache14592.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache14592.entries[idx n]?.getD (0, 0)).1| +
          (Cache14592.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm102

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm102_c : tableEnergyNumerator t wMm102 4 1 = (386937387304771876108871528333368785167134505769845773166592102187365389429205347556042167776492 : ℤ) := by
  exact KsIndex.NegSignProdFastMm102.eMm102_c_fast
theorem eMm102_r : tableEnergyRadius t wMm102 4 1 = (5469617405306780614847703006544718092679377064740409656518032254977748885528880000758965 : ℤ) := by
  exact KsIndex.NegSignProdFastMm102.eMm102_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm102_c
#print axioms KsIndex.NegSignProd.eMm102_r
