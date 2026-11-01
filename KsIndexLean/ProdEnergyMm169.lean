module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache18944

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm169 : Finset ℤ := Finset.Ioc (2623) (2687)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm169

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm169)

def idx (n : ℤ) : ℕ := (n - (2559)).toNat

lemma mem_wMm169 {n : ℤ} (hn : n ∈ wMm169) : (2623) < n ∧ n ≤ (2687) := by
  simpa only [wMm169, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm169) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm169 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm169) :
    2 * Cache18944.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm169 hn
  simp only [idx, Cache18944.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm169) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm169 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm169) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm169 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm169) :
    sampleNumerator (2 * n + 1) =
      (Cache18944.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache18944.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm169) :
    sampleRadius (2 * n + 1) =
      (Cache18944.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache18944.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm169_c_fast : tableEnergyNumerator t wMm169 4 1 = (2646935604203789792612879035660659639194330446477760945402540997972061591923467632543321065444447 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm169 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm169 4 1 =
      ∑ n ∈ wMm169, ((6 * n + 4) ^ 2 - 4) *
        ((Cache18944.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm169_r_fast : tableEnergyRadius t wMm169 4 1 = (8625188716352339535661834852371353243470318707771464992982553084409979977814872993642961 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm169 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm169 4 1 =
      ∑ n ∈ wMm169, (|((6 * n + 4) ^ 2 - 4)| * (Cache18944.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache18944.entries[idx n]?.getD (0, 0)).1| +
          (Cache18944.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm169

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm169_c : tableEnergyNumerator t wMm169 4 1 = (2646935604203789792612879035660659639194330446477760945402540997972061591923467632543321065444447 : ℤ) := by
  exact KsIndex.NegSignProdFastMm169.eMm169_c_fast
theorem eMm169_r : tableEnergyRadius t wMm169 4 1 = (8625188716352339535661834852371353243470318707771464992982553084409979977814872993642961 : ℤ) := by
  exact KsIndex.NegSignProdFastMm169.eMm169_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm169_c
#print axioms KsIndex.NegSignProd.eMm169_r
