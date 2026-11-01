module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache21248

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm204 : Finset ℤ := Finset.Ioc (4863) (4927)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm204

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm204)

def idx (n : ℤ) : ℕ := (n - (4863)).toNat

lemma mem_wMm204 {n : ℤ} (hn : n ∈ wMm204) : (4863) < n ∧ n ≤ (4927) := by
  simpa only [wMm204, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm204) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm204 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm204) :
    2 * Cache21248.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm204 hn
  simp only [idx, Cache21248.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm204) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm204 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm204) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm204 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm204) :
    sampleNumerator (2 * n + 1) =
      (Cache21248.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache21248.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm204) :
    sampleRadius (2 * n + 1) =
      (Cache21248.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache21248.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm204_c_fast : tableEnergyNumerator t wMm204 4 1 = (797642433854058671052177708309534370773204802291018721437699750831764918425022432821735529431326 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm204 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm204 4 1 =
      ∑ n ∈ wMm204, ((6 * n + 4) ^ 2 - 4) *
        ((Cache21248.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm204_r_fast : tableEnergyRadius t wMm204 4 1 = (2510723625554085862182575901263158301619680891138320489492149474658391578099717182632203 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm204 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm204 4 1 =
      ∑ n ∈ wMm204, (|((6 * n + 4) ^ 2 - 4)| * (Cache21248.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache21248.entries[idx n]?.getD (0, 0)).1| +
          (Cache21248.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm204

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm204_c : tableEnergyNumerator t wMm204 4 1 = (797642433854058671052177708309534370773204802291018721437699750831764918425022432821735529431326 : ℤ) := by
  exact KsIndex.NegSignProdFastMm204.eMm204_c_fast
theorem eMm204_r : tableEnergyRadius t wMm204 4 1 = (2510723625554085862182575901263158301619680891138320489492149474658391578099717182632203 : ℤ) := by
  exact KsIndex.NegSignProdFastMm204.eMm204_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm204_c
#print axioms KsIndex.NegSignProd.eMm204_r
