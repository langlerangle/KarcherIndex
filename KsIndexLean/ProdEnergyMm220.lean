module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache22272

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm220 : Finset ℤ := Finset.Ioc (5887) (5951)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm220

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm220)

def idx (n : ℤ) : ℕ := (n - (5887)).toNat

lemma mem_wMm220 {n : ℤ} (hn : n ∈ wMm220) : (5887) < n ∧ n ≤ (5951) := by
  simpa only [wMm220, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm220) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm220 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm220) :
    2 * Cache22272.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm220 hn
  simp only [idx, Cache22272.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm220) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm220 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm220) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm220 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm220) :
    sampleNumerator (2 * n + 1) =
      (Cache22272.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache22272.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm220) :
    sampleRadius (2 * n + 1) =
      (Cache22272.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache22272.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm220_c_fast : tableEnergyNumerator t wMm220 4 1 = (549950649589716927865908075713135727133478428289532236864425165099442075696472176847137700124155 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm220 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm220 4 1 =
      ∑ n ∈ wMm220, ((6 * n + 4) ^ 2 - 4) *
        ((Cache22272.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm220_r_fast : tableEnergyRadius t wMm220 4 1 = (1712448390362255677342589397905715996903409842082059292918677638318911882102266918373153 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm220 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm220 4 1 =
      ∑ n ∈ wMm220, (|((6 * n + 4) ^ 2 - 4)| * (Cache22272.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache22272.entries[idx n]?.getD (0, 0)).1| +
          (Cache22272.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm220

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm220_c : tableEnergyNumerator t wMm220 4 1 = (549950649589716927865908075713135727133478428289532236864425165099442075696472176847137700124155 : ℤ) := by
  exact KsIndex.NegSignProdFastMm220.eMm220_c_fast
theorem eMm220_r : tableEnergyRadius t wMm220 4 1 = (1712448390362255677342589397905715996903409842082059292918677638318911882102266918373153 : ℤ) := by
  exact KsIndex.NegSignProdFastMm220.eMm220_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm220_c
#print axioms KsIndex.NegSignProd.eMm220_r
