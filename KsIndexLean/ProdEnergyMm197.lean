module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache20736

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm197 : Finset ℤ := Finset.Ioc (4415) (4479)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm197

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm197)

def idx (n : ℤ) : ℕ := (n - (4351)).toNat

lemma mem_wMm197 {n : ℤ} (hn : n ∈ wMm197) : (4415) < n ∧ n ≤ (4479) := by
  simpa only [wMm197, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm197) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm197 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm197) :
    2 * Cache20736.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm197 hn
  simp only [idx, Cache20736.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm197) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm197 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm197) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm197 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm197) :
    sampleNumerator (2 * n + 1) =
      (Cache20736.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache20736.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm197) :
    sampleRadius (2 * n + 1) =
      (Cache20736.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache20736.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm197_c_fast : tableEnergyNumerator t wMm197 4 1 = (962620017057576202272890366327425107481311274410799951911893207256666034727112350878689641230674 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm197 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm197 4 1 =
      ∑ n ∈ wMm197, ((6 * n + 4) ^ 2 - 4) *
        ((Cache20736.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm197_r_fast : tableEnergyRadius t wMm197 4 1 = (3046590471942582407565066793115170858006084365733295035178160259760250221118494076192688 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm197 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm197 4 1 =
      ∑ n ∈ wMm197, (|((6 * n + 4) ^ 2 - 4)| * (Cache20736.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache20736.entries[idx n]?.getD (0, 0)).1| +
          (Cache20736.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm197

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm197_c : tableEnergyNumerator t wMm197 4 1 = (962620017057576202272890366327425107481311274410799951911893207256666034727112350878689641230674 : ℤ) := by
  exact KsIndex.NegSignProdFastMm197.eMm197_c_fast
theorem eMm197_r : tableEnergyRadius t wMm197 4 1 = (3046590471942582407565066793115170858006084365733295035178160259760250221118494076192688 : ℤ) := by
  exact KsIndex.NegSignProdFastMm197.eMm197_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm197_c
#print axioms KsIndex.NegSignProd.eMm197_r
