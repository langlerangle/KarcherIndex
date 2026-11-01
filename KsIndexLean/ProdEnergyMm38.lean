module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache10496

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm38 : Finset ℤ := Finset.Ioc (-5761) (-5697)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm38

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm38)

def idx (n : ℤ) : ℕ := (n - (-5889)).toNat

lemma mem_wMm38 {n : ℤ} (hn : n ∈ wMm38) : (-5761) < n ∧ n ≤ (-5697) := by
  simpa only [wMm38, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm38) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm38 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm38) :
    2 * Cache10496.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm38 hn
  simp only [idx, Cache10496.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm38) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm38 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm38) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm38 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm38) :
    sampleNumerator (2 * n + 1) =
      (Cache10496.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache10496.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm38) :
    sampleRadius (2 * n + 1) =
      (Cache10496.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache10496.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm38_c_fast : tableEnergyNumerator t wMm38 4 1 = (58309751065680231571113313701184234555601751841910963425816875135568458258556182999407518980374 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm38 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm38 4 1 =
      ∑ n ∈ wMm38, ((6 * n + 4) ^ 2 - 4) *
        ((Cache10496.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm38_r_fast : tableEnergyRadius t wMm38 4 1 = (576955092413714030001713996332915600739471589505715938039009255872485494505763298869699 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm38 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm38 4 1 =
      ∑ n ∈ wMm38, (|((6 * n + 4) ^ 2 - 4)| * (Cache10496.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache10496.entries[idx n]?.getD (0, 0)).1| +
          (Cache10496.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm38

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm38_c : tableEnergyNumerator t wMm38 4 1 = (58309751065680231571113313701184234555601751841910963425816875135568458258556182999407518980374 : ℤ) := by
  exact KsIndex.NegSignProdFastMm38.eMm38_c_fast
theorem eMm38_r : tableEnergyRadius t wMm38 4 1 = (576955092413714030001713996332915600739471589505715938039009255872485494505763298869699 : ℤ) := by
  exact KsIndex.NegSignProdFastMm38.eMm38_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm38_c
#print axioms KsIndex.NegSignProd.eMm38_r
