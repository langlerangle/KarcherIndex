module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache12544

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm69 : Finset ℤ := Finset.Ioc (-3777) (-3713)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm69

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm69)

def idx (n : ℤ) : ℕ := (n - (-3841)).toNat

lemma mem_wMm69 {n : ℤ} (hn : n ∈ wMm69) : (-3777) < n ∧ n ≤ (-3713) := by
  simpa only [wMm69, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm69) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm69 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm69) :
    2 * Cache12544.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm69 hn
  simp only [idx, Cache12544.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm69) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm69 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm69) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm69 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm69) :
    sampleNumerator (2 * n + 1) =
      (Cache12544.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache12544.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm69) :
    sampleRadius (2 * n + 1) =
      (Cache12544.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache12544.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm69_c_fast : tableEnergyNumerator t wMm69 4 1 = (112816249179116797232910673817647686776391250960093955230855173396288284037127018487278534065870 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm69 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm69 4 1 =
      ∑ n ∈ wMm69, ((6 * n + 4) ^ 2 - 4) *
        ((Cache12544.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm69_r_fast : tableEnergyRadius t wMm69 4 1 = (1246912912905315765793888767997229150910486070282390051660023970148532002938146386829119 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm69 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm69 4 1 =
      ∑ n ∈ wMm69, (|((6 * n + 4) ^ 2 - 4)| * (Cache12544.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache12544.entries[idx n]?.getD (0, 0)).1| +
          (Cache12544.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm69

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm69_c : tableEnergyNumerator t wMm69 4 1 = (112816249179116797232910673817647686776391250960093955230855173396288284037127018487278534065870 : ℤ) := by
  exact KsIndex.NegSignProdFastMm69.eMm69_c_fast
theorem eMm69_r : tableEnergyRadius t wMm69 4 1 = (1246912912905315765793888767997229150910486070282390051660023970148532002938146386829119 : ℤ) := by
  exact KsIndex.NegSignProdFastMm69.eMm69_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm69_c
#print axioms KsIndex.NegSignProd.eMm69_r
