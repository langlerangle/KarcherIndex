module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache8192

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm0 : Finset ℤ := Finset.Ioc (-8193) (-8129)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm0

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm0)

def idx (n : ℤ) : ℕ := (n - (-8193)).toNat

lemma mem_wMm0 {n : ℤ} (hn : n ∈ wMm0) : (-8193) < n ∧ n ≤ (-8129) := by
  simpa only [wMm0, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm0) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm0 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm0) :
    2 * Cache8192.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm0 hn
  simp only [idx, Cache8192.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm0) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm0 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm0) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm0 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm0) :
    sampleNumerator (2 * n + 1) =
      (Cache8192.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache8192.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm0) :
    sampleRadius (2 * n + 1) =
      (Cache8192.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache8192.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm0_c_fast : tableEnergyNumerator t wMm0 4 1 = (33278733540155643762526804405459371145211626764854094655749363281523396350015672386460098988202 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm0 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm0 4 1 =
      ∑ n ∈ wMm0, ((6 * n + 4) ^ 2 - 4) *
        ((Cache8192.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm0_r_fast : tableEnergyRadius t wMm0 4 1 = (302191972000367035418378905128079866412444547766104135213903728648433425648256486422780 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm0 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm0 4 1 =
      ∑ n ∈ wMm0, (|((6 * n + 4) ^ 2 - 4)| * (Cache8192.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache8192.entries[idx n]?.getD (0, 0)).1| +
          (Cache8192.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm0

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm0_c : tableEnergyNumerator t wMm0 4 1 = (33278733540155643762526804405459371145211626764854094655749363281523396350015672386460098988202 : ℤ) := by
  exact KsIndex.NegSignProdFastMm0.eMm0_c_fast
theorem eMm0_r : tableEnergyRadius t wMm0 4 1 = (302191972000367035418378905128079866412444547766104135213903728648433425648256486422780 : ℤ) := by
  exact KsIndex.NegSignProdFastMm0.eMm0_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm0_c
#print axioms KsIndex.NegSignProd.eMm0_r
