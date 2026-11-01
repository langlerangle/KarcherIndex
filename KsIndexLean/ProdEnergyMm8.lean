module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache8704

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm8 : Finset ℤ := Finset.Ioc (-7681) (-7617)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm8

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm8)

def idx (n : ℤ) : ℕ := (n - (-7681)).toNat

lemma mem_wMm8 {n : ℤ} (hn : n ∈ wMm8) : (-7681) < n ∧ n ≤ (-7617) := by
  simpa only [wMm8, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm8) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm8 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm8) :
    2 * Cache8704.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm8 hn
  simp only [idx, Cache8704.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm8) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm8 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm8) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm8 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm8) :
    sampleNumerator (2 * n + 1) =
      (Cache8704.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache8704.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm8) :
    sampleRadius (2 * n + 1) =
      (Cache8704.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache8704.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm8_c_fast : tableEnergyNumerator t wMm8 4 1 = (36904305462228074892237179269969071979449927587091820640802172164905734872551470931229380727649 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm8 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm8 4 1 =
      ∑ n ∈ wMm8, ((6 * n + 4) ^ 2 - 4) *
        ((Cache8704.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm8_r_fast : tableEnergyRadius t wMm8 4 1 = (340292647735267595777924093046490953244196774534269892121226064433223924544805151514665 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm8 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm8 4 1 =
      ∑ n ∈ wMm8, (|((6 * n + 4) ^ 2 - 4)| * (Cache8704.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache8704.entries[idx n]?.getD (0, 0)).1| +
          (Cache8704.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm8

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm8_c : tableEnergyNumerator t wMm8 4 1 = (36904305462228074892237179269969071979449927587091820640802172164905734872551470931229380727649 : ℤ) := by
  exact KsIndex.NegSignProdFastMm8.eMm8_c_fast
theorem eMm8_r : tableEnergyRadius t wMm8 4 1 = (340292647735267595777924093046490953244196774534269892121226064433223924544805151514665 : ℤ) := by
  exact KsIndex.NegSignProdFastMm8.eMm8_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm8_c
#print axioms KsIndex.NegSignProd.eMm8_r
