module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache19456

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm176 : Finset ℤ := Finset.Ioc (3071) (3135)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm176

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm176)

def idx (n : ℤ) : ℕ := (n - (3071)).toNat

lemma mem_wMm176 {n : ℤ} (hn : n ∈ wMm176) : (3071) < n ∧ n ≤ (3135) := by
  simpa only [wMm176, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm176) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm176 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm176) :
    2 * Cache19456.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm176 hn
  simp only [idx, Cache19456.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm176) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm176 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm176) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm176 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm176) :
    sampleNumerator (2 * n + 1) =
      (Cache19456.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache19456.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm176) :
    sampleRadius (2 * n + 1) =
      (Cache19456.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache19456.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm176_c_fast : tableEnergyNumerator t wMm176 4 1 = (1949151762896889991729265804498581368901718794945102090393861820973254454740033438338178153916248 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm176 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm176 4 1 =
      ∑ n ∈ wMm176, ((6 * n + 4) ^ 2 - 4) *
        ((Cache19456.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm176_r_fast : tableEnergyRadius t wMm176 4 1 = (6295835646513467679739659086160443221920001183381986191434603488405258613836353989718012 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm176 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm176 4 1 =
      ∑ n ∈ wMm176, (|((6 * n + 4) ^ 2 - 4)| * (Cache19456.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache19456.entries[idx n]?.getD (0, 0)).1| +
          (Cache19456.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm176

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm176_c : tableEnergyNumerator t wMm176 4 1 = (1949151762896889991729265804498581368901718794945102090393861820973254454740033438338178153916248 : ℤ) := by
  exact KsIndex.NegSignProdFastMm176.eMm176_c_fast
theorem eMm176_r : tableEnergyRadius t wMm176 4 1 = (6295835646513467679739659086160443221920001183381986191434603488405258613836353989718012 : ℤ) := by
  exact KsIndex.NegSignProdFastMm176.eMm176_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm176_c
#print axioms KsIndex.NegSignProd.eMm176_r
