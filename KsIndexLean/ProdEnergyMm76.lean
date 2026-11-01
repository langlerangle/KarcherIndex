module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache13056

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm76 : Finset ℤ := Finset.Ioc (-3329) (-3265)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm76

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm76)

def idx (n : ℤ) : ℕ := (n - (-3329)).toNat

lemma mem_wMm76 {n : ℤ} (hn : n ∈ wMm76) : (-3329) < n ∧ n ≤ (-3265) := by
  simpa only [wMm76, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm76) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm76 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm76) :
    2 * Cache13056.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm76 hn
  simp only [idx, Cache13056.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm76) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm76 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm76) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm76 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm76) :
    sampleNumerator (2 * n + 1) =
      (Cache13056.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache13056.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm76) :
    sampleRadius (2 * n + 1) =
      (Cache13056.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache13056.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm76_c_fast : tableEnergyNumerator t wMm76 4 1 = (137029482036297699019179735599366220508790810011170976094523856353660345812673307342508964116641 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm76 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm76 4 1 =
      ∑ n ∈ wMm76, ((6 * n + 4) ^ 2 - 4) *
        ((Cache13056.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm76_r_fast : tableEnergyRadius t wMm76 4 1 = (1568442550934318711501908540779414213421463173681395815320399371701746309109687200925752 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm76 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm76 4 1 =
      ∑ n ∈ wMm76, (|((6 * n + 4) ^ 2 - 4)| * (Cache13056.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache13056.entries[idx n]?.getD (0, 0)).1| +
          (Cache13056.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm76

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm76_c : tableEnergyNumerator t wMm76 4 1 = (137029482036297699019179735599366220508790810011170976094523856353660345812673307342508964116641 : ℤ) := by
  exact KsIndex.NegSignProdFastMm76.eMm76_c_fast
theorem eMm76_r : tableEnergyRadius t wMm76 4 1 = (1568442550934318711501908540779414213421463173681395815320399371701746309109687200925752 : ℤ) := by
  exact KsIndex.NegSignProdFastMm76.eMm76_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm76_c
#print axioms KsIndex.NegSignProd.eMm76_r
