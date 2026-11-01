module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache14336

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm96 : Finset ℤ := Finset.Ioc (-2049) (-1985)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm96

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm96)

def idx (n : ℤ) : ℕ := (n - (-2049)).toNat

lemma mem_wMm96 {n : ℤ} (hn : n ∈ wMm96) : (-2049) < n ∧ n ≤ (-1985) := by
  simpa only [wMm96, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm96) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm96 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm96) :
    2 * Cache14336.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm96 hn
  simp only [idx, Cache14336.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm96) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm96 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm96) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm96 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm96) :
    sampleNumerator (2 * n + 1) =
      (Cache14336.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache14336.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm96) :
    sampleRadius (2 * n + 1) =
      (Cache14336.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache14336.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm96_c_fast : tableEnergyNumerator t wMm96 4 1 = (285136800904395177401694022429118590452868165568609943909753708366361558312309629093620101522013 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm96 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm96 4 1 =
      ∑ n ∈ wMm96, ((6 * n + 4) ^ 2 - 4) *
        ((Cache14336.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm96_r_fast : tableEnergyRadius t wMm96 4 1 = (3769331837915318823004588411220297063677281314492343776673606297245345106266254318147302 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm96 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm96 4 1 =
      ∑ n ∈ wMm96, (|((6 * n + 4) ^ 2 - 4)| * (Cache14336.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache14336.entries[idx n]?.getD (0, 0)).1| +
          (Cache14336.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm96

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm96_c : tableEnergyNumerator t wMm96 4 1 = (285136800904395177401694022429118590452868165568609943909753708366361558312309629093620101522013 : ℤ) := by
  exact KsIndex.NegSignProdFastMm96.eMm96_c_fast
theorem eMm96_r : tableEnergyRadius t wMm96 4 1 = (3769331837915318823004588411220297063677281314492343776673606297245345106266254318147302 : ℤ) := by
  exact KsIndex.NegSignProdFastMm96.eMm96_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm96_c
#print axioms KsIndex.NegSignProd.eMm96_r
