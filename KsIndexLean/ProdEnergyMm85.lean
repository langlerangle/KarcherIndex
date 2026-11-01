module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache13568

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm85 : Finset ℤ := Finset.Ioc (-2753) (-2689)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm85

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm85)

def idx (n : ℤ) : ℕ := (n - (-2817)).toNat

lemma mem_wMm85 {n : ℤ} (hn : n ∈ wMm85) : (-2753) < n ∧ n ≤ (-2689) := by
  simpa only [wMm85, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm85) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm85 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm85) :
    2 * Cache13568.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm85 hn
  simp only [idx, Cache13568.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm85) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm85 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm85) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm85 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm85) :
    sampleNumerator (2 * n + 1) =
      (Cache13568.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache13568.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm85) :
    sampleRadius (2 * n + 1) =
      (Cache13568.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache13568.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm85_c_fast : tableEnergyNumerator t wMm85 4 1 = (183082564552203120161324119040077698752170527265240347498169305934621754936982069476151868731140 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm85 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm85 4 1 =
      ∑ n ∈ wMm85, ((6 * n + 4) ^ 2 - 4) *
        ((Cache13568.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm85_r_fast : tableEnergyRadius t wMm85 4 1 = (2212874571829398687910595252514914243779378949574886551152829637418568368881968240499149 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm85 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm85 4 1 =
      ∑ n ∈ wMm85, (|((6 * n + 4) ^ 2 - 4)| * (Cache13568.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache13568.entries[idx n]?.getD (0, 0)).1| +
          (Cache13568.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm85

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm85_c : tableEnergyNumerator t wMm85 4 1 = (183082564552203120161324119040077698752170527265240347498169305934621754936982069476151868731140 : ℤ) := by
  exact KsIndex.NegSignProdFastMm85.eMm85_c_fast
theorem eMm85_r : tableEnergyRadius t wMm85 4 1 = (2212874571829398687910595252514914243779378949574886551152829637418568368881968240499149 : ℤ) := by
  exact KsIndex.NegSignProdFastMm85.eMm85_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm85_c
#print axioms KsIndex.NegSignProd.eMm85_r
