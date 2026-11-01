module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache12288

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm65 : Finset ℤ := Finset.Ioc (-4033) (-3969)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm65

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm65)

def idx (n : ℤ) : ℕ := (n - (-4097)).toNat

lemma mem_wMm65 {n : ℤ} (hn : n ∈ wMm65) : (-4033) < n ∧ n ≤ (-3969) := by
  simpa only [wMm65, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm65) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm65 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm65) :
    2 * Cache12288.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm65 hn
  simp only [idx, Cache12288.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm65) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm65 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm65) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm65 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm65) :
    sampleNumerator (2 * n + 1) =
      (Cache12288.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache12288.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm65) :
    sampleRadius (2 * n + 1) =
      (Cache12288.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache12288.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm65_c_fast : tableEnergyNumerator t wMm65 4 1 = (101921901359441335665395931380690161107638036256285567819594856559683444211540549020145557178914 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm65 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm65 4 1 =
      ∑ n ∈ wMm65, ((6 * n + 4) ^ 2 - 4) *
        ((Cache12288.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm65_r_fast : tableEnergyRadius t wMm65 4 1 = (1106620512431414506248941609351003215699950727074542076993349189012278083769728807622697 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm65 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm65 4 1 =
      ∑ n ∈ wMm65, (|((6 * n + 4) ^ 2 - 4)| * (Cache12288.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache12288.entries[idx n]?.getD (0, 0)).1| +
          (Cache12288.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm65

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm65_c : tableEnergyNumerator t wMm65 4 1 = (101921901359441335665395931380690161107638036256285567819594856559683444211540549020145557178914 : ℤ) := by
  exact KsIndex.NegSignProdFastMm65.eMm65_c_fast
theorem eMm65_r : tableEnergyRadius t wMm65 4 1 = (1106620512431414506248941609351003215699950727074542076993349189012278083769728807622697 : ℤ) := by
  exact KsIndex.NegSignProdFastMm65.eMm65_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm65_c
#print axioms KsIndex.NegSignProd.eMm65_r
