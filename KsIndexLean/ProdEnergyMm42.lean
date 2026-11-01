module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache10752

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm42 : Finset ℤ := Finset.Ioc (-5505) (-5441)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm42

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm42)

def idx (n : ℤ) : ℕ := (n - (-5633)).toNat

lemma mem_wMm42 {n : ℤ} (hn : n ∈ wMm42) : (-5505) < n ∧ n ≤ (-5441) := by
  simpa only [wMm42, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm42) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm42 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm42) :
    2 * Cache10752.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm42 hn
  simp only [idx, Cache10752.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm42) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm42 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm42) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm42 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm42) :
    sampleNumerator (2 * n + 1) =
      (Cache10752.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache10752.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm42) :
    sampleRadius (2 * n + 1) =
      (Cache10752.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache10752.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm42_c_fast : tableEnergyNumerator t wMm42 4 1 = (62646491051754542154111389993214104844704605330714966692362876116612002216859432551394301803605 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm42 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm42 4 1 =
      ∑ n ∈ wMm42, ((6 * n + 4) ^ 2 - 4) *
        ((Cache10752.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm42_r_fast : tableEnergyRadius t wMm42 4 1 = (627026384019343509460185500034215651626307825577288327255550544101847953324092563116200 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm42 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm42 4 1 =
      ∑ n ∈ wMm42, (|((6 * n + 4) ^ 2 - 4)| * (Cache10752.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache10752.entries[idx n]?.getD (0, 0)).1| +
          (Cache10752.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm42

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm42_c : tableEnergyNumerator t wMm42 4 1 = (62646491051754542154111389993214104844704605330714966692362876116612002216859432551394301803605 : ℤ) := by
  exact KsIndex.NegSignProdFastMm42.eMm42_c_fast
theorem eMm42_r : tableEnergyRadius t wMm42 4 1 = (627026384019343509460185500034215651626307825577288327255550544101847953324092563116200 : ℤ) := by
  exact KsIndex.NegSignProdFastMm42.eMm42_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm42_c
#print axioms KsIndex.NegSignProd.eMm42_r
