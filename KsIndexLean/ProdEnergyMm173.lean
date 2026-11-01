module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache19200

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm173 : Finset ℤ := Finset.Ioc (2879) (2943)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm173

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm173)

def idx (n : ℤ) : ℕ := (n - (2815)).toNat

lemma mem_wMm173 {n : ℤ} (hn : n ∈ wMm173) : (2879) < n ∧ n ≤ (2943) := by
  simpa only [wMm173, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm173) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm173 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm173) :
    2 * Cache19200.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm173 hn
  simp only [idx, Cache19200.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm173) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm173 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm173) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm173 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm173) :
    sampleNumerator (2 * n + 1) =
      (Cache19200.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache19200.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm173) :
    sampleRadius (2 * n + 1) =
      (Cache19200.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache19200.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm173_c_fast : tableEnergyNumerator t wMm173 4 1 = (2209404658239689540677723634570938810589069326176133944172525773740117390732311886943742922436753 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm173 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm173 4 1 =
      ∑ n ∈ wMm173, ((6 * n + 4) ^ 2 - 4) *
        ((Cache19200.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm173_r_fast : tableEnergyRadius t wMm173 4 1 = (7162226398225428124027157694360160165806789050608285283909741111938101576143451504580442 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm173 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm173 4 1 =
      ∑ n ∈ wMm173, (|((6 * n + 4) ^ 2 - 4)| * (Cache19200.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache19200.entries[idx n]?.getD (0, 0)).1| +
          (Cache19200.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm173

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm173_c : tableEnergyNumerator t wMm173 4 1 = (2209404658239689540677723634570938810589069326176133944172525773740117390732311886943742922436753 : ℤ) := by
  exact KsIndex.NegSignProdFastMm173.eMm173_c_fast
theorem eMm173_r : tableEnergyRadius t wMm173 4 1 = (7162226398225428124027157694360160165806789050608285283909741111938101576143451504580442 : ℤ) := by
  exact KsIndex.NegSignProdFastMm173.eMm173_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm173_c
#print axioms KsIndex.NegSignProd.eMm173_r
