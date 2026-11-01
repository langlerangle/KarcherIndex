module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache16384

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm130 : Finset ℤ := Finset.Ioc (127) (191)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm130

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm130)

def idx (n : ℤ) : ℕ := (n - (-1)).toNat

lemma mem_wMm130 {n : ℤ} (hn : n ∈ wMm130) : (127) < n ∧ n ≤ (191) := by
  simpa only [wMm130, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm130) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm130 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm130) :
    2 * Cache16384.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm130 hn
  simp only [idx, Cache16384.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm130) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm130 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm130) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm130 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm130) :
    sampleNumerator (2 * n + 1) =
      (Cache16384.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache16384.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm130) :
    sampleRadius (2 * n + 1) =
      (Cache16384.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache16384.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm130_c_fast : tableEnergyNumerator t wMm130 4 1 = (708214660625670693819422891954940055894519200424917914959389537939257604050612494861592080826367189 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm130 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm130 4 1 =
      ∑ n ∈ wMm130, ((6 * n + 4) ^ 2 - 4) *
        ((Cache16384.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm130_r_fast : tableEnergyRadius t wMm130 4 1 = (2696617708461248541702916247981124496260676927623576504936081934479947961570728200484415828 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm130 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm130 4 1 =
      ∑ n ∈ wMm130, (|((6 * n + 4) ^ 2 - 4)| * (Cache16384.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache16384.entries[idx n]?.getD (0, 0)).1| +
          (Cache16384.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm130

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm130_c : tableEnergyNumerator t wMm130 4 1 = (708214660625670693819422891954940055894519200424917914959389537939257604050612494861592080826367189 : ℤ) := by
  exact KsIndex.NegSignProdFastMm130.eMm130_c_fast
theorem eMm130_r : tableEnergyRadius t wMm130 4 1 = (2696617708461248541702916247981124496260676927623576504936081934479947961570728200484415828 : ℤ) := by
  exact KsIndex.NegSignProdFastMm130.eMm130_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm130_c
#print axioms KsIndex.NegSignProd.eMm130_r
