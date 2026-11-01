module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache12288

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm64 : Finset ℤ := Finset.Ioc (-4097) (-4033)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm64

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm64)

def idx (n : ℤ) : ℕ := (n - (-4097)).toNat

lemma mem_wMm64 {n : ℤ} (hn : n ∈ wMm64) : (-4097) < n ∧ n ≤ (-4033) := by
  simpa only [wMm64, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm64) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm64 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm64) :
    2 * Cache12288.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm64 hn
  simp only [idx, Cache12288.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm64) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm64 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm64) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm64 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm64) :
    sampleNumerator (2 * n + 1) =
      (Cache12288.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache12288.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm64) :
    sampleRadius (2 * n + 1) =
      (Cache12288.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache12288.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm64_c_fast : tableEnergyNumerator t wMm64 4 1 = (99461493581179292044112604225033877074068733936951242342334051460296657591367020355288708682338 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm64 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm64 4 1 =
      ∑ n ∈ wMm64, ((6 * n + 4) ^ 2 - 4) *
        ((Cache12288.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm64_r_fast : tableEnergyRadius t wMm64 4 1 = (1075338015411433462218376566228451897662159472187045165081248267313936071031421412155279 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm64 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm64 4 1 =
      ∑ n ∈ wMm64, (|((6 * n + 4) ^ 2 - 4)| * (Cache12288.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache12288.entries[idx n]?.getD (0, 0)).1| +
          (Cache12288.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm64

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm64_c : tableEnergyNumerator t wMm64 4 1 = (99461493581179292044112604225033877074068733936951242342334051460296657591367020355288708682338 : ℤ) := by
  exact KsIndex.NegSignProdFastMm64.eMm64_c_fast
theorem eMm64_r : tableEnergyRadius t wMm64 4 1 = (1075338015411433462218376566228451897662159472187045165081248267313936071031421412155279 : ℤ) := by
  exact KsIndex.NegSignProdFastMm64.eMm64_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm64_c
#print axioms KsIndex.NegSignProd.eMm64_r
