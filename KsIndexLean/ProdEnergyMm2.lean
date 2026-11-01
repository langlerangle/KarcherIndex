module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache8192

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm2 : Finset ℤ := Finset.Ioc (-8065) (-8001)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm2

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm2)

def idx (n : ℤ) : ℕ := (n - (-8193)).toNat

lemma mem_wMm2 {n : ℤ} (hn : n ∈ wMm2) : (-8065) < n ∧ n ≤ (-8001) := by
  simpa only [wMm2, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm2) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm2 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm2) :
    2 * Cache8192.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm2 hn
  simp only [idx, Cache8192.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm2) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm2 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm2) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm2 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm2) :
    sampleNumerator (2 * n + 1) =
      (Cache8192.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache8192.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm2) :
    sampleRadius (2 * n + 1) =
      (Cache8192.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache8192.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm2_c_fast : tableEnergyNumerator t wMm2 4 1 = (34130028368543767131704389605701969163667212357078541359945450029994342420201863346010418434184 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm2 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm2 4 1 =
      ∑ n ∈ wMm2, ((6 * n + 4) ^ 2 - 4) *
        ((Cache8192.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm2_r_fast : tableEnergyRadius t wMm2 4 1 = (311079187553327939150098573964328945253538222406835323676312007317131110246144125238012 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm2 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm2 4 1 =
      ∑ n ∈ wMm2, (|((6 * n + 4) ^ 2 - 4)| * (Cache8192.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache8192.entries[idx n]?.getD (0, 0)).1| +
          (Cache8192.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm2

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm2_c : tableEnergyNumerator t wMm2 4 1 = (34130028368543767131704389605701969163667212357078541359945450029994342420201863346010418434184 : ℤ) := by
  exact KsIndex.NegSignProdFastMm2.eMm2_c_fast
theorem eMm2_r : tableEnergyRadius t wMm2 4 1 = (311079187553327939150098573964328945253538222406835323676312007317131110246144125238012 : ℤ) := by
  exact KsIndex.NegSignProdFastMm2.eMm2_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm2_c
#print axioms KsIndex.NegSignProd.eMm2_r
