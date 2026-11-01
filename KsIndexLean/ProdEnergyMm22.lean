module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache9472

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm22 : Finset ℤ := Finset.Ioc (-6785) (-6721)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm22

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm22)

def idx (n : ℤ) : ℕ := (n - (-6913)).toNat

lemma mem_wMm22 {n : ℤ} (hn : n ∈ wMm22) : (-6785) < n ∧ n ≤ (-6721) := by
  simpa only [wMm22, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm22) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm22 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm22) :
    2 * Cache9472.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm22 hn
  simp only [idx, Cache9472.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm22) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm22 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm22) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm22 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm22) :
    sampleNumerator (2 * n + 1) =
      (Cache9472.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache9472.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm22) :
    sampleRadius (2 * n + 1) =
      (Cache9472.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache9472.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm22_c_fast : tableEnergyNumerator t wMm22 4 1 = (44983819899291042507407406541096074813474912012154661887662170775901211655583263506635409081458 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm22 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm22 4 1 =
      ∑ n ∈ wMm22, ((6 * n + 4) ^ 2 - 4) *
        ((Cache9472.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm22_r_fast : tableEnergyRadius t wMm22 4 1 = (427409933195987093231538898219537419210640816736281231415162870180305380978654909022595 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm22 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm22 4 1 =
      ∑ n ∈ wMm22, (|((6 * n + 4) ^ 2 - 4)| * (Cache9472.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache9472.entries[idx n]?.getD (0, 0)).1| +
          (Cache9472.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm22

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm22_c : tableEnergyNumerator t wMm22 4 1 = (44983819899291042507407406541096074813474912012154661887662170775901211655583263506635409081458 : ℤ) := by
  exact KsIndex.NegSignProdFastMm22.eMm22_c_fast
theorem eMm22_r : tableEnergyRadius t wMm22 4 1 = (427409933195987093231538898219537419210640816736281231415162870180305380978654909022595 : ℤ) := by
  exact KsIndex.NegSignProdFastMm22.eMm22_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm22_c
#print axioms KsIndex.NegSignProd.eMm22_r
