module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache20480

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm193 : Finset ℤ := Finset.Ioc (4159) (4223)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm193

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm193)

def idx (n : ℤ) : ℕ := (n - (4095)).toNat

lemma mem_wMm193 {n : ℤ} (hn : n ∈ wMm193) : (4159) < n ∧ n ≤ (4223) := by
  simpa only [wMm193, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm193) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm193 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm193) :
    2 * Cache20480.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm193 hn
  simp only [idx, Cache20480.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm193) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm193 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm193) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm193 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm193) :
    sampleNumerator (2 * n + 1) =
      (Cache20480.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache20480.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm193) :
    sampleRadius (2 * n + 1) =
      (Cache20480.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache20480.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm193_c_fast : tableEnergyNumerator t wMm193 4 1 = (1081196340180053529743181400467235175826634765363035912389013390085257915824140995504886351997650 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm193 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm193 4 1 =
      ∑ n ∈ wMm193, ((6 * n + 4) ^ 2 - 4) *
        ((Cache20480.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm193_r_fast : tableEnergyRadius t wMm193 4 1 = (3433405645825052137081332439936396640579474271267856817335469573616867333895677467738614 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm193 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm193 4 1 =
      ∑ n ∈ wMm193, (|((6 * n + 4) ^ 2 - 4)| * (Cache20480.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache20480.entries[idx n]?.getD (0, 0)).1| +
          (Cache20480.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm193

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm193_c : tableEnergyNumerator t wMm193 4 1 = (1081196340180053529743181400467235175826634765363035912389013390085257915824140995504886351997650 : ℤ) := by
  exact KsIndex.NegSignProdFastMm193.eMm193_c_fast
theorem eMm193_r : tableEnergyRadius t wMm193 4 1 = (3433405645825052137081332439936396640579474271267856817335469573616867333895677467738614 : ℤ) := by
  exact KsIndex.NegSignProdFastMm193.eMm193_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm193_c
#print axioms KsIndex.NegSignProd.eMm193_r
