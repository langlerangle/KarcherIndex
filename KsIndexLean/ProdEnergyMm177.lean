module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache19456

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm177 : Finset ℤ := Finset.Ioc (3135) (3199)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm177

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm177)

def idx (n : ℤ) : ℕ := (n - (3071)).toNat

lemma mem_wMm177 {n : ℤ} (hn : n ∈ wMm177) : (3135) < n ∧ n ≤ (3199) := by
  simpa only [wMm177, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm177) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm177 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm177) :
    2 * Cache19456.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm177 hn
  simp only [idx, Cache19456.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm177) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm177 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm177) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm177 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm177) :
    sampleNumerator (2 * n + 1) =
      (Cache19456.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache19456.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm177) :
    sampleRadius (2 * n + 1) =
      (Cache19456.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache19456.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm177_c_fast : tableEnergyNumerator t wMm177 4 1 = (1872628211054240691569852743626908857539961271009655283792902696009008726804832445768475195853377 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm177 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm177 4 1 =
      ∑ n ∈ wMm177, ((6 * n + 4) ^ 2 - 4) *
        ((Cache19456.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm177_r_fast : tableEnergyRadius t wMm177 4 1 = (6041693582343266614217240389290624769381791602875485690232864979737101912168322722039225 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm177 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm177 4 1 =
      ∑ n ∈ wMm177, (|((6 * n + 4) ^ 2 - 4)| * (Cache19456.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache19456.entries[idx n]?.getD (0, 0)).1| +
          (Cache19456.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm177

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm177_c : tableEnergyNumerator t wMm177 4 1 = (1872628211054240691569852743626908857539961271009655283792902696009008726804832445768475195853377 : ℤ) := by
  exact KsIndex.NegSignProdFastMm177.eMm177_c_fast
theorem eMm177_r : tableEnergyRadius t wMm177 4 1 = (6041693582343266614217240389290624769381791602875485690232864979737101912168322722039225 : ℤ) := by
  exact KsIndex.NegSignProdFastMm177.eMm177_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm177_c
#print axioms KsIndex.NegSignProd.eMm177_r
