module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache19200

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm174 : Finset ℤ := Finset.Ioc (2943) (3007)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm174

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm174)

def idx (n : ℤ) : ℕ := (n - (2815)).toNat

lemma mem_wMm174 {n : ℤ} (hn : n ∈ wMm174) : (2943) < n ∧ n ≤ (3007) := by
  simpa only [wMm174, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm174) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm174 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm174) :
    2 * Cache19200.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm174 hn
  simp only [idx, Cache19200.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm174) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm174 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm174) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm174 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm174) :
    sampleNumerator (2 * n + 1) =
      (Cache19200.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache19200.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm174) :
    sampleRadius (2 * n + 1) =
      (Cache19200.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache19200.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm174_c_fast : tableEnergyNumerator t wMm174 4 1 = (2117100465700359524358176037154885168290340976865591655333462403227015944749871152538109859859969 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm174 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm174 4 1 =
      ∑ n ∈ wMm174, ((6 * n + 4) ^ 2 - 4) *
        ((Cache19200.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm174_r_fast : tableEnergyRadius t wMm174 4 1 = (6854591410600522844788058601210764253253808353656914994984326265790300297628695029418196 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm174 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm174 4 1 =
      ∑ n ∈ wMm174, (|((6 * n + 4) ^ 2 - 4)| * (Cache19200.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache19200.entries[idx n]?.getD (0, 0)).1| +
          (Cache19200.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm174

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm174_c : tableEnergyNumerator t wMm174 4 1 = (2117100465700359524358176037154885168290340976865591655333462403227015944749871152538109859859969 : ℤ) := by
  exact KsIndex.NegSignProdFastMm174.eMm174_c_fast
theorem eMm174_r : tableEnergyRadius t wMm174 4 1 = (6854591410600522844788058601210764253253808353656914994984326265790300297628695029418196 : ℤ) := by
  exact KsIndex.NegSignProdFastMm174.eMm174_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm174_c
#print axioms KsIndex.NegSignProd.eMm174_r
