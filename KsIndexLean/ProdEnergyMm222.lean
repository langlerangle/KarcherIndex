module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache22272

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm222 : Finset ℤ := Finset.Ioc (6015) (6079)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm222

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm222)

def idx (n : ℤ) : ℕ := (n - (5887)).toNat

lemma mem_wMm222 {n : ℤ} (hn : n ∈ wMm222) : (6015) < n ∧ n ≤ (6079) := by
  simpa only [wMm222, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm222) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm222 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm222) :
    2 * Cache22272.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm222 hn
  simp only [idx, Cache22272.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm222) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm222 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm222) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm222 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm222) :
    sampleNumerator (2 * n + 1) =
      (Cache22272.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache22272.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm222) :
    sampleRadius (2 * n + 1) =
      (Cache22272.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache22272.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm222_c_fast : tableEnergyNumerator t wMm222 4 1 = (527403782723818024818015411695131099225686295155128262782012928484121129695993565255896873483355 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm222 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm222 4 1 =
      ∑ n ∈ wMm222, ((6 * n + 4) ^ 2 - 4) *
        ((Cache22272.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm222_r_fast : tableEnergyRadius t wMm222 4 1 = (1640239373388072929386024063924969092415280640072537229421413597339378242730563166150945 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm222 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm222 4 1 =
      ∑ n ∈ wMm222, (|((6 * n + 4) ^ 2 - 4)| * (Cache22272.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache22272.entries[idx n]?.getD (0, 0)).1| +
          (Cache22272.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm222

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm222_c : tableEnergyNumerator t wMm222 4 1 = (527403782723818024818015411695131099225686295155128262782012928484121129695993565255896873483355 : ℤ) := by
  exact KsIndex.NegSignProdFastMm222.eMm222_c_fast
theorem eMm222_r : tableEnergyRadius t wMm222 4 1 = (1640239373388072929386024063924969092415280640072537229421413597339378242730563166150945 : ℤ) := by
  exact KsIndex.NegSignProdFastMm222.eMm222_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm222_c
#print axioms KsIndex.NegSignProd.eMm222_r
