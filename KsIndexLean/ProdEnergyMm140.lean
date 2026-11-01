module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache17152

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm140 : Finset ℤ := Finset.Ioc (767) (831)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm140

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm140)

def idx (n : ℤ) : ℕ := (n - (767)).toNat

lemma mem_wMm140 {n : ℤ} (hn : n ∈ wMm140) : (767) < n ∧ n ≤ (831) := by
  simpa only [wMm140, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm140) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm140 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm140) :
    2 * Cache17152.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm140 hn
  simp only [idx, Cache17152.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm140) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm140 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm140) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm140 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm140) :
    sampleNumerator (2 * n + 1) =
      (Cache17152.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache17152.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm140) :
    sampleRadius (2 * n + 1) =
      (Cache17152.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache17152.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm140_c_fast : tableEnergyNumerator t wMm140 4 1 = (28138515631911266415249573563333881883481105690655144290669086489411161466273530080145926014068041 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm140 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm140 4 1 =
      ∑ n ∈ wMm140, ((6 * n + 4) ^ 2 - 4) *
        ((Cache17152.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm140_r_fast : tableEnergyRadius t wMm140 4 1 = (98028688955231990699991485820663402030335714963901719464632896209788610440237021814814776 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm140 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm140 4 1 =
      ∑ n ∈ wMm140, (|((6 * n + 4) ^ 2 - 4)| * (Cache17152.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache17152.entries[idx n]?.getD (0, 0)).1| +
          (Cache17152.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm140

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm140_c : tableEnergyNumerator t wMm140 4 1 = (28138515631911266415249573563333881883481105690655144290669086489411161466273530080145926014068041 : ℤ) := by
  exact KsIndex.NegSignProdFastMm140.eMm140_c_fast
theorem eMm140_r : tableEnergyRadius t wMm140 4 1 = (98028688955231990699991485820663402030335714963901719464632896209788610440237021814814776 : ℤ) := by
  exact KsIndex.NegSignProdFastMm140.eMm140_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm140_c
#print axioms KsIndex.NegSignProd.eMm140_r
