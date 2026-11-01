module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache20480

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm192 : Finset ℤ := Finset.Ioc (4095) (4159)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm192

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm192)

def idx (n : ℤ) : ℕ := (n - (4095)).toNat

lemma mem_wMm192 {n : ℤ} (hn : n ∈ wMm192) : (4095) < n ∧ n ≤ (4159) := by
  simpa only [wMm192, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm192) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm192 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm192) :
    2 * Cache20480.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm192 hn
  simp only [idx, Cache20480.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm192) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm192 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm192) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm192 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm192) :
    sampleNumerator (2 * n + 1) =
      (Cache20480.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache20480.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm192) :
    sampleRadius (2 * n + 1) =
      (Cache20480.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache20480.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm192_c_fast : tableEnergyNumerator t wMm192 4 1 = (1114296114393392539261132262527567169053094255782145150969311330740560094171850787156918229461943 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm192 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm192 4 1 =
      ∑ n ∈ wMm192, ((6 * n + 4) ^ 2 - 4) *
        ((Cache20480.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm192_r_fast : tableEnergyRadius t wMm192 4 1 = (3541605962880449969218254693923832587479182672463314123763336868593048835452826218741593 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm192 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm192 4 1 =
      ∑ n ∈ wMm192, (|((6 * n + 4) ^ 2 - 4)| * (Cache20480.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache20480.entries[idx n]?.getD (0, 0)).1| +
          (Cache20480.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm192

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm192_c : tableEnergyNumerator t wMm192 4 1 = (1114296114393392539261132262527567169053094255782145150969311330740560094171850787156918229461943 : ℤ) := by
  exact KsIndex.NegSignProdFastMm192.eMm192_c_fast
theorem eMm192_r : tableEnergyRadius t wMm192 4 1 = (3541605962880449969218254693923832587479182672463314123763336868593048835452826218741593 : ℤ) := by
  exact KsIndex.NegSignProdFastMm192.eMm192_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm192_c
#print axioms KsIndex.NegSignProd.eMm192_r
