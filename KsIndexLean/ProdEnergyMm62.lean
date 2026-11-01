module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache12032

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm62 : Finset ℤ := Finset.Ioc (-4225) (-4161)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm62

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm62)

def idx (n : ℤ) : ℕ := (n - (-4353)).toNat

lemma mem_wMm62 {n : ℤ} (hn : n ∈ wMm62) : (-4225) < n ∧ n ≤ (-4161) := by
  simpa only [wMm62, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm62) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm62 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm62) :
    2 * Cache12032.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm62 hn
  simp only [idx, Cache12032.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm62) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm62 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm62) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm62 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm62) :
    sampleNumerator (2 * n + 1) =
      (Cache12032.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache12032.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm62) :
    sampleRadius (2 * n + 1) =
      (Cache12032.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache12032.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm62_c_fast : tableEnergyNumerator t wMm62 4 1 = (94818240529455116382396561249058072474076969216055985840990962096611475357583689283974116767095 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm62 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm62 4 1 =
      ∑ n ∈ wMm62, ((6 * n + 4) ^ 2 - 4) *
        ((Cache12032.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm62_r_fast : tableEnergyRadius t wMm62 4 1 = (1016719679681302034733457150960188918793341740464239380807408112587348490502352090683567 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm62 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm62 4 1 =
      ∑ n ∈ wMm62, (|((6 * n + 4) ^ 2 - 4)| * (Cache12032.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache12032.entries[idx n]?.getD (0, 0)).1| +
          (Cache12032.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm62

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm62_c : tableEnergyNumerator t wMm62 4 1 = (94818240529455116382396561249058072474076969216055985840990962096611475357583689283974116767095 : ℤ) := by
  exact KsIndex.NegSignProdFastMm62.eMm62_c_fast
theorem eMm62_r : tableEnergyRadius t wMm62 4 1 = (1016719679681302034733457150960188918793341740464239380807408112587348490502352090683567 : ℤ) := by
  exact KsIndex.NegSignProdFastMm62.eMm62_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm62_c
#print axioms KsIndex.NegSignProd.eMm62_r
