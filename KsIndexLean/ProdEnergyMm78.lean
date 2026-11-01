module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache13056

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm78 : Finset ℤ := Finset.Ioc (-3201) (-3137)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm78

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm78)

def idx (n : ℤ) : ℕ := (n - (-3329)).toNat

lemma mem_wMm78 {n : ℤ} (hn : n ∈ wMm78) : (-3201) < n ∧ n ≤ (-3137) := by
  simpa only [wMm78, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm78) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm78 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm78) :
    2 * Cache13056.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm78 hn
  simp only [idx, Cache13056.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm78) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm78 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm78) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm78 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm78) :
    sampleNumerator (2 * n + 1) =
      (Cache13056.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache13056.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm78) :
    sampleRadius (2 * n + 1) =
      (Cache13056.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache13056.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm78_c_fast : tableEnergyNumerator t wMm78 4 1 = (145514883767143248731180951564498512166415500864381652069328964474373053385970378327468198797174 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm78 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm78 4 1 =
      ∑ n ∈ wMm78, ((6 * n + 4) ^ 2 - 4) *
        ((Cache13056.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm78_r_fast : tableEnergyRadius t wMm78 4 1 = (1684081934809622592105104116306151164740654989081834321522007343248579427927055033600344 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm78 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm78 4 1 =
      ∑ n ∈ wMm78, (|((6 * n + 4) ^ 2 - 4)| * (Cache13056.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache13056.entries[idx n]?.getD (0, 0)).1| +
          (Cache13056.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm78

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm78_c : tableEnergyNumerator t wMm78 4 1 = (145514883767143248731180951564498512166415500864381652069328964474373053385970378327468198797174 : ℤ) := by
  exact KsIndex.NegSignProdFastMm78.eMm78_c_fast
theorem eMm78_r : tableEnergyRadius t wMm78 4 1 = (1684081934809622592105104116306151164740654989081834321522007343248579427927055033600344 : ℤ) := by
  exact KsIndex.NegSignProdFastMm78.eMm78_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm78_c
#print axioms KsIndex.NegSignProd.eMm78_r
