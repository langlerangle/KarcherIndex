module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache9728

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm25 : Finset ℤ := Finset.Ioc (-6593) (-6529)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm25

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm25)

def idx (n : ℤ) : ℕ := (n - (-6657)).toNat

lemma mem_wMm25 {n : ℤ} (hn : n ∈ wMm25) : (-6593) < n ∧ n ≤ (-6529) := by
  simpa only [wMm25, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm25) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm25 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm25) :
    2 * Cache9728.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm25 hn
  simp only [idx, Cache9728.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm25) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm25 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm25) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm25 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm25) :
    sampleNumerator (2 * n + 1) =
      (Cache9728.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache9728.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm25) :
    sampleRadius (2 * n + 1) =
      (Cache9728.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache9728.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm25_c_fast : tableEnergyNumerator t wMm25 4 1 = (47085648111881670244269406077046117608898011012622153033111180523861694885282796478057035853145 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm25 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm25 4 1 =
      ∑ n ∈ wMm25, ((6 * n + 4) ^ 2 - 4) *
        ((Cache9728.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm25_r_fast : tableEnergyRadius t wMm25 4 1 = (450535927581169710116905809060291204482287003806148272351573568556488398984769020798787 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm25 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm25 4 1 =
      ∑ n ∈ wMm25, (|((6 * n + 4) ^ 2 - 4)| * (Cache9728.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache9728.entries[idx n]?.getD (0, 0)).1| +
          (Cache9728.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm25

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm25_c : tableEnergyNumerator t wMm25 4 1 = (47085648111881670244269406077046117608898011012622153033111180523861694885282796478057035853145 : ℤ) := by
  exact KsIndex.NegSignProdFastMm25.eMm25_c_fast
theorem eMm25_r : tableEnergyRadius t wMm25 4 1 = (450535927581169710116905809060291204482287003806148272351573568556488398984769020798787 : ℤ) := by
  exact KsIndex.NegSignProdFastMm25.eMm25_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm25_c
#print axioms KsIndex.NegSignProd.eMm25_r
