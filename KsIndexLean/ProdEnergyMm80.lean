module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache13312

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm80 : Finset ℤ := Finset.Ioc (-3073) (-3009)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm80

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm80)

def idx (n : ℤ) : ℕ := (n - (-3073)).toNat

lemma mem_wMm80 {n : ℤ} (hn : n ∈ wMm80) : (-3073) < n ∧ n ≤ (-3009) := by
  simpa only [wMm80, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm80) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm80 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm80) :
    2 * Cache13312.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm80 hn
  simp only [idx, Cache13312.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm80) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm80 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm80) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm80 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm80) :
    sampleNumerator (2 * n + 1) =
      (Cache13312.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache13312.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm80) :
    sampleRadius (2 * n + 1) =
      (Cache13312.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache13312.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm80_c_fast : tableEnergyNumerator t wMm80 4 1 = (154881157945775345337792485960865749578792658344489713559210167462094352076410008877388158610333 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm80 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm80 4 1 =
      ∑ n ∈ wMm80, ((6 * n + 4) ^ 2 - 4) *
        ((Cache13312.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm80_r_fast : tableEnergyRadius t wMm80 4 1 = (1813407178049505333280248399181682211263820053965805824739296024251186628689039608744905 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm80 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm80 4 1 =
      ∑ n ∈ wMm80, (|((6 * n + 4) ^ 2 - 4)| * (Cache13312.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache13312.entries[idx n]?.getD (0, 0)).1| +
          (Cache13312.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm80

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm80_c : tableEnergyNumerator t wMm80 4 1 = (154881157945775345337792485960865749578792658344489713559210167462094352076410008877388158610333 : ℤ) := by
  exact KsIndex.NegSignProdFastMm80.eMm80_c_fast
theorem eMm80_r : tableEnergyRadius t wMm80 4 1 = (1813407178049505333280248399181682211263820053965805824739296024251186628689039608744905 : ℤ) := by
  exact KsIndex.NegSignProdFastMm80.eMm80_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm80_c
#print axioms KsIndex.NegSignProd.eMm80_r
