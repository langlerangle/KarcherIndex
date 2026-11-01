module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache22016

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm218 : Finset ℤ := Finset.Ioc (5759) (5823)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm218

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm218)

def idx (n : ℤ) : ℕ := (n - (5631)).toNat

lemma mem_wMm218 {n : ℤ} (hn : n ∈ wMm218) : (5759) < n ∧ n ≤ (5823) := by
  simpa only [wMm218, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm218) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm218 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm218) :
    2 * Cache22016.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm218 hn
  simp only [idx, Cache22016.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm218) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm218 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm218) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm218 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm218) :
    sampleNumerator (2 * n + 1) =
      (Cache22016.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache22016.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm218) :
    sampleRadius (2 * n + 1) =
      (Cache22016.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache22016.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm218_c_fast : tableEnergyNumerator t wMm218 4 1 = (573988664363222362778100130102809213584664967013240271876449051643841277426111715885244233091316 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm218 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm218 4 1 =
      ∑ n ∈ wMm218, ((6 * n + 4) ^ 2 - 4) *
        ((Cache22016.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm218_r_fast : tableEnergyRadius t wMm218 4 1 = (1789527165349925097728727005994673716710336471074595268075399172475779713059483896391986 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm218 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm218 4 1 =
      ∑ n ∈ wMm218, (|((6 * n + 4) ^ 2 - 4)| * (Cache22016.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache22016.entries[idx n]?.getD (0, 0)).1| +
          (Cache22016.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm218

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm218_c : tableEnergyNumerator t wMm218 4 1 = (573988664363222362778100130102809213584664967013240271876449051643841277426111715885244233091316 : ℤ) := by
  exact KsIndex.NegSignProdFastMm218.eMm218_c_fast
theorem eMm218_r : tableEnergyRadius t wMm218 4 1 = (1789527165349925097728727005994673716710336471074595268075399172475779713059483896391986 : ℤ) := by
  exact KsIndex.NegSignProdFastMm218.eMm218_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm218_c
#print axioms KsIndex.NegSignProd.eMm218_r
