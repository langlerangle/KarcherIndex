module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache14336

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm98 : Finset ℤ := Finset.Ioc (-1921) (-1857)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm98

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm98)

def idx (n : ℤ) : ℕ := (n - (-2049)).toNat

lemma mem_wMm98 {n : ℤ} (hn : n ∈ wMm98) : (-1921) < n ∧ n ≤ (-1857) := by
  simpa only [wMm98, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm98) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm98 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm98) :
    2 * Cache14336.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm98 hn
  simp only [idx, Cache14336.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm98) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm98 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm98) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm98 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm98) :
    sampleNumerator (2 * n + 1) =
      (Cache14336.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache14336.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm98) :
    sampleRadius (2 * n + 1) =
      (Cache14336.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache14336.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm98_c_fast : tableEnergyNumerator t wMm98 4 1 = (313697173264579274960032244814817827950434362268544928426456238785184641968470402092078690491315 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm98 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm98 4 1 =
      ∑ n ∈ wMm98, ((6 * n + 4) ^ 2 - 4) *
        ((Cache14336.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm98_r_fast : tableEnergyRadius t wMm98 4 1 = (4232534204421123078365972752823607898846848217588657037507551921786412950980069075534084 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm98 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm98 4 1 =
      ∑ n ∈ wMm98, (|((6 * n + 4) ^ 2 - 4)| * (Cache14336.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache14336.entries[idx n]?.getD (0, 0)).1| +
          (Cache14336.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm98

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm98_c : tableEnergyNumerator t wMm98 4 1 = (313697173264579274960032244814817827950434362268544928426456238785184641968470402092078690491315 : ℤ) := by
  exact KsIndex.NegSignProdFastMm98.eMm98_c_fast
theorem eMm98_r : tableEnergyRadius t wMm98 4 1 = (4232534204421123078365972752823607898846848217588657037507551921786412950980069075534084 : ℤ) := by
  exact KsIndex.NegSignProdFastMm98.eMm98_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm98_c
#print axioms KsIndex.NegSignProd.eMm98_r
