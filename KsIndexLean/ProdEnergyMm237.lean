module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache23296

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm237 : Finset ℤ := Finset.Ioc (6975) (7039)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm237

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm237)

def idx (n : ℤ) : ℕ := (n - (6911)).toNat

lemma mem_wMm237 {n : ℤ} (hn : n ∈ wMm237) : (6975) < n ∧ n ≤ (7039) := by
  simpa only [wMm237, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm237) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm237 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm237) :
    2 * Cache23296.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm237 hn
  simp only [idx, Cache23296.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm237) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm237 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm237) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm237 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm237) :
    sampleNumerator (2 * n + 1) =
      (Cache23296.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache23296.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm237) :
    sampleRadius (2 * n + 1) =
      (Cache23296.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache23296.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm237_c_fast : tableEnergyNumerator t wMm237 4 1 = (395344513450158425630733344846745997587524576532066935912372737135972456252081433507878934023516 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm237 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm237 4 1 =
      ∑ n ∈ wMm237, ((6 * n + 4) ^ 2 - 4) *
        ((Cache23296.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm237_r_fast : tableEnergyRadius t wMm237 4 1 = (1219234157496676400592709401412337863580783670641626484134214671504247724067165266360149 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm237 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm237 4 1 =
      ∑ n ∈ wMm237, (|((6 * n + 4) ^ 2 - 4)| * (Cache23296.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache23296.entries[idx n]?.getD (0, 0)).1| +
          (Cache23296.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm237

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm237_c : tableEnergyNumerator t wMm237 4 1 = (395344513450158425630733344846745997587524576532066935912372737135972456252081433507878934023516 : ℤ) := by
  exact KsIndex.NegSignProdFastMm237.eMm237_c_fast
theorem eMm237_r : tableEnergyRadius t wMm237 4 1 = (1219234157496676400592709401412337863580783670641626484134214671504247724067165266360149 : ℤ) := by
  exact KsIndex.NegSignProdFastMm237.eMm237_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm237_c
#print axioms KsIndex.NegSignProd.eMm237_r
