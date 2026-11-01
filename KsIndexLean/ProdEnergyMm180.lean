module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache19712

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm180 : Finset ℤ := Finset.Ioc (3327) (3391)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm180

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm180)

def idx (n : ℤ) : ℕ := (n - (3327)).toNat

lemma mem_wMm180 {n : ℤ} (hn : n ∈ wMm180) : (3327) < n ∧ n ≤ (3391) := by
  simpa only [wMm180, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm180) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm180 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm180) :
    2 * Cache19712.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm180 hn
  simp only [idx, Cache19712.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm180) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm180 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm180) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm180 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm180) :
    sampleNumerator (2 * n + 1) =
      (Cache19712.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache19712.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm180) :
    sampleRadius (2 * n + 1) =
      (Cache19712.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache19712.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm180_c_fast : tableEnergyNumerator t wMm180 4 1 = (1668444354562601007973707889114562194477478128792387050704250365205708250765185438870429029720801 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm180 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm180 4 1 =
      ∑ n ∈ wMm180, ((6 * n + 4) ^ 2 - 4) *
        ((Cache19712.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm180_r_fast : tableEnergyRadius t wMm180 4 1 = (5365060902098827523671826415306463410080269661189150344900288853960138286222608825353441 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm180 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm180 4 1 =
      ∑ n ∈ wMm180, (|((6 * n + 4) ^ 2 - 4)| * (Cache19712.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache19712.entries[idx n]?.getD (0, 0)).1| +
          (Cache19712.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm180

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm180_c : tableEnergyNumerator t wMm180 4 1 = (1668444354562601007973707889114562194477478128792387050704250365205708250765185438870429029720801 : ℤ) := by
  exact KsIndex.NegSignProdFastMm180.eMm180_c_fast
theorem eMm180_r : tableEnergyRadius t wMm180 4 1 = (5365060902098827523671826415306463410080269661189150344900288853960138286222608825353441 : ℤ) := by
  exact KsIndex.NegSignProdFastMm180.eMm180_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm180_c
#print axioms KsIndex.NegSignProd.eMm180_r
