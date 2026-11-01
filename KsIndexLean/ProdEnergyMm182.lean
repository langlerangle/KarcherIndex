module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache19712

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm182 : Finset ℤ := Finset.Ioc (3455) (3519)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm182

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm182)

def idx (n : ℤ) : ℕ := (n - (3327)).toNat

lemma mem_wMm182 {n : ℤ} (hn : n ∈ wMm182) : (3455) < n ∧ n ≤ (3519) := by
  simpa only [wMm182, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm182) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm182 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm182) :
    2 * Cache19712.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm182 hn
  simp only [idx, Cache19712.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm182) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm182 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm182) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm182 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm182) :
    sampleNumerator (2 * n + 1) =
      (Cache19712.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache19712.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm182) :
    sampleRadius (2 * n + 1) =
      (Cache19712.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache19712.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm182_c_fast : tableEnergyNumerator t wMm182 4 1 = (1550455846276200778971308499853660705490635236664787225057962365544686868299071523378252468933829 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm182 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm182 4 1 =
      ∑ n ∈ wMm182, ((6 * n + 4) ^ 2 - 4) *
        ((Cache19712.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm182_r_fast : tableEnergyRadius t wMm182 4 1 = (4975124500114981585959634824779034260654351558111120596628369504503706436141802641561401 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm182 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm182 4 1 =
      ∑ n ∈ wMm182, (|((6 * n + 4) ^ 2 - 4)| * (Cache19712.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache19712.entries[idx n]?.getD (0, 0)).1| +
          (Cache19712.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm182

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm182_c : tableEnergyNumerator t wMm182 4 1 = (1550455846276200778971308499853660705490635236664787225057962365544686868299071523378252468933829 : ℤ) := by
  exact KsIndex.NegSignProdFastMm182.eMm182_c_fast
theorem eMm182_r : tableEnergyRadius t wMm182 4 1 = (4975124500114981585959634824779034260654351558111120596628369504503706436141802641561401 : ℤ) := by
  exact KsIndex.NegSignProdFastMm182.eMm182_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm182_c
#print axioms KsIndex.NegSignProd.eMm182_r
