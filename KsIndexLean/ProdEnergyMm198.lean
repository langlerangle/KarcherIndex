module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache20736

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm198 : Finset ℤ := Finset.Ioc (4479) (4543)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm198

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm198)

def idx (n : ℤ) : ℕ := (n - (4351)).toNat

lemma mem_wMm198 {n : ℤ} (hn : n ∈ wMm198) : (4479) < n ∧ n ≤ (4543) := by
  simpa only [wMm198, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm198) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm198 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm198) :
    2 * Cache20736.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm198 hn
  simp only [idx, Cache20736.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm198) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm198 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm198) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm198 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm198) :
    sampleNumerator (2 * n + 1) =
      (Cache20736.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache20736.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm198) :
    sampleRadius (2 * n + 1) =
      (Cache20736.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache20736.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm198_c_fast : tableEnergyNumerator t wMm198 4 1 = (936048157947184559775082132533949402142581161113561638181404942756427617784708227851924627116184 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm198 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm198 4 1 =
      ∑ n ∈ wMm198, ((6 * n + 4) ^ 2 - 4) *
        ((Cache20736.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm198_r_fast : tableEnergyRadius t wMm198 4 1 = (2960090548113022457988491708711944814515015294024799260215593108016935201956646828194732 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm198 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm198 4 1 =
      ∑ n ∈ wMm198, (|((6 * n + 4) ^ 2 - 4)| * (Cache20736.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache20736.entries[idx n]?.getD (0, 0)).1| +
          (Cache20736.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm198

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm198_c : tableEnergyNumerator t wMm198 4 1 = (936048157947184559775082132533949402142581161113561638181404942756427617784708227851924627116184 : ℤ) := by
  exact KsIndex.NegSignProdFastMm198.eMm198_c_fast
theorem eMm198_r : tableEnergyRadius t wMm198 4 1 = (2960090548113022457988491708711944814515015294024799260215593108016935201956646828194732 : ℤ) := by
  exact KsIndex.NegSignProdFastMm198.eMm198_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm198_c
#print axioms KsIndex.NegSignProd.eMm198_r
