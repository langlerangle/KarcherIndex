module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache16128

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm125 : Finset ℤ := Finset.Ioc (-193) (-129)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm125

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm125)

def idx (n : ℤ) : ℕ := (n - (-257)).toNat

lemma mem_wMm125 {n : ℤ} (hn : n ∈ wMm125) : (-193) < n ∧ n ≤ (-129) := by
  simpa only [wMm125, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm125) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm125 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm125) :
    2 * Cache16128.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm125 hn
  simp only [idx, Cache16128.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm125) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm125 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm125) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm125 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm125) :
    sampleNumerator (2 * n + 1) =
      (Cache16128.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache16128.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm125) :
    sampleRadius (2 * n + 1) =
      (Cache16128.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache16128.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm125_c_fast : tableEnergyNumerator t wMm125 4 1 = (4823153609832558423660890066337817037374165655552835973783211106758409523760197340352534906098258 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm125 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm125 4 1 =
      ∑ n ∈ wMm125, ((6 * n + 4) ^ 2 - 4) *
        ((Cache16128.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm125_r_fast : tableEnergyRadius t wMm125 4 1 = (221173440017776361285365358747391447782113382895725460146607621912719379888819234299446278 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm125 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm125 4 1 =
      ∑ n ∈ wMm125, (|((6 * n + 4) ^ 2 - 4)| * (Cache16128.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache16128.entries[idx n]?.getD (0, 0)).1| +
          (Cache16128.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm125

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm125_c : tableEnergyNumerator t wMm125 4 1 = (4823153609832558423660890066337817037374165655552835973783211106758409523760197340352534906098258 : ℤ) := by
  exact KsIndex.NegSignProdFastMm125.eMm125_c_fast
theorem eMm125_r : tableEnergyRadius t wMm125 4 1 = (221173440017776361285365358747391447782113382895725460146607621912719379888819234299446278 : ℤ) := by
  exact KsIndex.NegSignProdFastMm125.eMm125_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm125_c
#print axioms KsIndex.NegSignProd.eMm125_r
