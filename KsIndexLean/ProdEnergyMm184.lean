module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache19968

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm184 : Finset ℤ := Finset.Ioc (3583) (3647)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm184

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm184)

def idx (n : ℤ) : ℕ := (n - (3583)).toNat

lemma mem_wMm184 {n : ℤ} (hn : n ∈ wMm184) : (3583) < n ∧ n ≤ (3647) := by
  simpa only [wMm184, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm184) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm184 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm184) :
    2 * Cache19968.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm184 hn
  simp only [idx, Cache19968.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm184) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm184 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm184) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm184 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm184) :
    sampleNumerator (2 * n + 1) =
      (Cache19968.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache19968.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm184) :
    sampleRadius (2 * n + 1) =
      (Cache19968.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache19968.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm184_c_fast : tableEnergyNumerator t wMm184 4 1 = (1444641600332524586002509420967597226849695587933541550457121788263529746677408039319000716821538 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm184 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm184 4 1 =
      ∑ n ∈ wMm184, ((6 * n + 4) ^ 2 - 4) *
        ((Cache19968.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm184_r_fast : tableEnergyRadius t wMm184 4 1 = (4626140979793468379179734403218145563486366405807351102705343161699073482972756905479361 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm184 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm184 4 1 =
      ∑ n ∈ wMm184, (|((6 * n + 4) ^ 2 - 4)| * (Cache19968.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache19968.entries[idx n]?.getD (0, 0)).1| +
          (Cache19968.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm184

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm184_c : tableEnergyNumerator t wMm184 4 1 = (1444641600332524586002509420967597226849695587933541550457121788263529746677408039319000716821538 : ℤ) := by
  exact KsIndex.NegSignProdFastMm184.eMm184_c_fast
theorem eMm184_r : tableEnergyRadius t wMm184 4 1 = (4626140979793468379179734403218145563486366405807351102705343161699073482972756905479361 : ℤ) := by
  exact KsIndex.NegSignProdFastMm184.eMm184_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm184_c
#print axioms KsIndex.NegSignProd.eMm184_r
