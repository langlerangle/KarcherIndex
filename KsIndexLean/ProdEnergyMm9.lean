module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache8704

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm9 : Finset ℤ := Finset.Ioc (-7617) (-7553)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm9

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm9)

def idx (n : ℤ) : ℕ := (n - (-7681)).toNat

lemma mem_wMm9 {n : ℤ} (hn : n ∈ wMm9) : (-7617) < n ∧ n ≤ (-7553) := by
  simpa only [wMm9, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm9) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm9 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm9) :
    2 * Cache8704.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm9 hn
  simp only [idx, Cache8704.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm9) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm9 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm9) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm9 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm9) :
    sampleNumerator (2 * n + 1) =
      (Cache8704.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache8704.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm9) :
    sampleRadius (2 * n + 1) =
      (Cache8704.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache8704.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm9_c_fast : tableEnergyNumerator t wMm9 4 1 = (37401701452008772767652135439930610229138326858850480275054344927755524376968592490724290517819 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm9 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm9 4 1 =
      ∑ n ∈ wMm9, ((6 * n + 4) ^ 2 - 4) *
        ((Cache8704.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm9_r_fast : tableEnergyRadius t wMm9 4 1 = (345569830008328196688737918028386580820834466240969980935487163199342843224211463842757 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm9 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm9 4 1 =
      ∑ n ∈ wMm9, (|((6 * n + 4) ^ 2 - 4)| * (Cache8704.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache8704.entries[idx n]?.getD (0, 0)).1| +
          (Cache8704.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm9

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm9_c : tableEnergyNumerator t wMm9 4 1 = (37401701452008772767652135439930610229138326858850480275054344927755524376968592490724290517819 : ℤ) := by
  exact KsIndex.NegSignProdFastMm9.eMm9_c_fast
theorem eMm9_r : tableEnergyRadius t wMm9 4 1 = (345569830008328196688737918028386580820834466240969980935487163199342843224211463842757 : ℤ) := by
  exact KsIndex.NegSignProdFastMm9.eMm9_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm9_c
#print axioms KsIndex.NegSignProd.eMm9_r
