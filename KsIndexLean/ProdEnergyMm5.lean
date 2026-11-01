module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache8448

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm5 : Finset ℤ := Finset.Ioc (-7873) (-7809)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm5

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm5)

def idx (n : ℤ) : ℕ := (n - (-7937)).toNat

lemma mem_wMm5 {n : ℤ} (hn : n ∈ wMm5) : (-7873) < n ∧ n ≤ (-7809) := by
  simpa only [wMm5, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm5) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm5 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm5) :
    2 * Cache8448.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm5 hn
  simp only [idx, Cache8448.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm5) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm5 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm5) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm5 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm5) :
    sampleNumerator (2 * n + 1) =
      (Cache8448.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache8448.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm5) :
    sampleRadius (2 * n + 1) =
      (Cache8448.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache8448.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm5_c_fast : tableEnergyNumerator t wMm5 4 1 = (35473864256798956672767907718643614511241018865887065665457565103859743768865498912744639850842 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm5 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm5 4 1 =
      ∑ n ∈ wMm5, ((6 * n + 4) ^ 2 - 4) *
        ((Cache8448.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm5_r_fast : tableEnergyRadius t wMm5 4 1 = (325182652165340235639911046504503106627720515286604637369454301415663214372332331839244 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm5 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm5 4 1 =
      ∑ n ∈ wMm5, (|((6 * n + 4) ^ 2 - 4)| * (Cache8448.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache8448.entries[idx n]?.getD (0, 0)).1| +
          (Cache8448.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm5

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm5_c : tableEnergyNumerator t wMm5 4 1 = (35473864256798956672767907718643614511241018865887065665457565103859743768865498912744639850842 : ℤ) := by
  exact KsIndex.NegSignProdFastMm5.eMm5_c_fast
theorem eMm5_r : tableEnergyRadius t wMm5 4 1 = (325182652165340235639911046504503106627720515286604637369454301415663214372332331839244 : ℤ) := by
  exact KsIndex.NegSignProdFastMm5.eMm5_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm5_c
#print axioms KsIndex.NegSignProd.eMm5_r
