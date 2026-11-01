module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache22528

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm226 : Finset ℤ := Finset.Ioc (6271) (6335)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm226

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm226)

def idx (n : ℤ) : ℕ := (n - (6143)).toNat

lemma mem_wMm226 {n : ℤ} (hn : n ∈ wMm226) : (6271) < n ∧ n ≤ (6335) := by
  simpa only [wMm226, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm226) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm226 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm226) :
    2 * Cache22528.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm226 hn
  simp only [idx, Cache22528.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm226) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm226 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm226) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm226 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm226) :
    sampleNumerator (2 * n + 1) =
      (Cache22528.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache22528.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm226) :
    sampleRadius (2 * n + 1) =
      (Cache22528.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache22528.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm226_c_fast : tableEnergyNumerator t wMm226 4 1 = (486310498959016981964424610912308454883482025472113649931328722351273146591308674397396952655254 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm226 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm226 4 1 =
      ∑ n ∈ wMm226, ((6 * n + 4) ^ 2 - 4) *
        ((Cache22528.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm226_r_fast : tableEnergyRadius t wMm226 4 1 = (1508865378881950024350246762276544487756165937800875682957147233815410418156957225887817 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm226 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm226 4 1 =
      ∑ n ∈ wMm226, (|((6 * n + 4) ^ 2 - 4)| * (Cache22528.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache22528.entries[idx n]?.getD (0, 0)).1| +
          (Cache22528.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm226

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm226_c : tableEnergyNumerator t wMm226 4 1 = (486310498959016981964424610912308454883482025472113649931328722351273146591308674397396952655254 : ℤ) := by
  exact KsIndex.NegSignProdFastMm226.eMm226_c_fast
theorem eMm226_r : tableEnergyRadius t wMm226 4 1 = (1508865378881950024350246762276544487756165937800875682957147233815410418156957225887817 : ℤ) := by
  exact KsIndex.NegSignProdFastMm226.eMm226_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm226_c
#print axioms KsIndex.NegSignProd.eMm226_r
