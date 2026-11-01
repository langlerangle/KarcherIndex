module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache11264

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm48 : Finset ℤ := Finset.Ioc (-5121) (-5057)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm48

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm48)

def idx (n : ℤ) : ℕ := (n - (-5121)).toNat

lemma mem_wMm48 {n : ℤ} (hn : n ∈ wMm48) : (-5121) < n ∧ n ≤ (-5057) := by
  simpa only [wMm48, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm48) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm48 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm48) :
    2 * Cache11264.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm48 hn
  simp only [idx, Cache11264.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm48) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm48 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm48) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm48 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm48) :
    sampleNumerator (2 * n + 1) =
      (Cache11264.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache11264.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm48) :
    sampleRadius (2 * n + 1) =
      (Cache11264.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache11264.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm48_c_fast : tableEnergyNumerator t wMm48 4 1 = (70196717049085915318594566539326161243594351816057389349735940925747061031972332160036119110529 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm48 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm48 4 1 =
      ∑ n ∈ wMm48, ((6 * n + 4) ^ 2 - 4) *
        ((Cache11264.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm48_r_fast : tableEnergyRadius t wMm48 4 1 = (715697529719268797883276183601735910054944117366229581541855761610379484480012525882498 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm48 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm48 4 1 =
      ∑ n ∈ wMm48, (|((6 * n + 4) ^ 2 - 4)| * (Cache11264.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache11264.entries[idx n]?.getD (0, 0)).1| +
          (Cache11264.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm48

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm48_c : tableEnergyNumerator t wMm48 4 1 = (70196717049085915318594566539326161243594351816057389349735940925747061031972332160036119110529 : ℤ) := by
  exact KsIndex.NegSignProdFastMm48.eMm48_c_fast
theorem eMm48_r : tableEnergyRadius t wMm48 4 1 = (715697529719268797883276183601735910054944117366229581541855761610379484480012525882498 : ℤ) := by
  exact KsIndex.NegSignProdFastMm48.eMm48_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm48_c
#print axioms KsIndex.NegSignProd.eMm48_r
