module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache17664

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm148 : Finset ℤ := Finset.Ioc (1279) (1343)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm148

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm148)

def idx (n : ℤ) : ℕ := (n - (1279)).toNat

lemma mem_wMm148 {n : ℤ} (hn : n ∈ wMm148) : (1279) < n ∧ n ≤ (1343) := by
  simpa only [wMm148, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm148) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm148 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm148) :
    2 * Cache17664.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm148 hn
  simp only [idx, Cache17664.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm148) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm148 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm148) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm148 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm148) :
    sampleNumerator (2 * n + 1) =
      (Cache17664.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache17664.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm148) :
    sampleRadius (2 * n + 1) =
      (Cache17664.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache17664.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm148_c_fast : tableEnergyNumerator t wMm148 4 1 = (10599517248621542393866388063584920236844617265100862966103169338560563683713298588522742464901156 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm148 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm148 4 1 =
      ∑ n ∈ wMm148, ((6 * n + 4) ^ 2 - 4) *
        ((Cache17664.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm148_r_fast : tableEnergyRadius t wMm148 4 1 = (35929432744199866936134702218198699918572584204697982380194726634790770175197813074204495 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm148 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm148 4 1 =
      ∑ n ∈ wMm148, (|((6 * n + 4) ^ 2 - 4)| * (Cache17664.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache17664.entries[idx n]?.getD (0, 0)).1| +
          (Cache17664.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm148

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm148_c : tableEnergyNumerator t wMm148 4 1 = (10599517248621542393866388063584920236844617265100862966103169338560563683713298588522742464901156 : ℤ) := by
  exact KsIndex.NegSignProdFastMm148.eMm148_c_fast
theorem eMm148_r : tableEnergyRadius t wMm148 4 1 = (35929432744199866936134702218198699918572584204697982380194726634790770175197813074204495 : ℤ) := by
  exact KsIndex.NegSignProdFastMm148.eMm148_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm148_c
#print axioms KsIndex.NegSignProd.eMm148_r
