module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache16384

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm128 : Finset ℤ := Finset.Ioc (-1) (63)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm128

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm128)

def idx (n : ℤ) : ℕ := (n - (-1)).toNat

lemma mem_wMm128 {n : ℤ} (hn : n ∈ wMm128) : (-1) < n ∧ n ≤ (63) := by
  simpa only [wMm128, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm128) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm128 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm128) :
    2 * Cache16384.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm128 hn
  simp only [idx, Cache16384.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm128) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm128 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm128) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm128 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm128) :
    sampleNumerator (2 * n + 1) =
      (Cache16384.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache16384.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm128) :
    sampleRadius (2 * n + 1) =
      (Cache16384.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache16384.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm128_c_fast : tableEnergyNumerator t wMm128 4 1 = (1217405699524181951292345457616043138787509349542580579973584240074832411331878082223428617939286528268 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm128 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm128 4 1 =
      ∑ n ∈ wMm128, ((6 * n + 4) ^ 2 - 4) *
        ((Cache16384.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm128_r_fast : tableEnergyRadius t wMm128 4 1 = (7917808181881773866284461191362795477781205013335867728942796860038733831035753757152497787741 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm128 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm128 4 1 =
      ∑ n ∈ wMm128, (|((6 * n + 4) ^ 2 - 4)| * (Cache16384.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache16384.entries[idx n]?.getD (0, 0)).1| +
          (Cache16384.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm128

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm128_c : tableEnergyNumerator t wMm128 4 1 = (1217405699524181951292345457616043138787509349542580579973584240074832411331878082223428617939286528268 : ℤ) := by
  exact KsIndex.NegSignProdFastMm128.eMm128_c_fast
theorem eMm128_r : tableEnergyRadius t wMm128 4 1 = (7917808181881773866284461191362795477781205013335867728942796860038733831035753757152497787741 : ℤ) := by
  exact KsIndex.NegSignProdFastMm128.eMm128_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm128_c
#print axioms KsIndex.NegSignProd.eMm128_r
