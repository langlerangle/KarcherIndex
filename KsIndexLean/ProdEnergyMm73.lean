module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache12800

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm73 : Finset ℤ := Finset.Ioc (-3521) (-3457)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm73

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm73)

def idx (n : ℤ) : ℕ := (n - (-3585)).toNat

lemma mem_wMm73 {n : ℤ} (hn : n ∈ wMm73) : (-3521) < n ∧ n ≤ (-3457) := by
  simpa only [wMm73, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm73) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm73 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm73) :
    2 * Cache12800.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm73 hn
  simp only [idx, Cache12800.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm73) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm73 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm73) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm73 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm73) :
    sampleNumerator (2 * n + 1) =
      (Cache12800.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache12800.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm73) :
    sampleRadius (2 * n + 1) =
      (Cache12800.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache12800.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm73_c_fast : tableEnergyNumerator t wMm73 4 1 = (125715699375745876596462573691597464873389781595406999544555001233407742090039241512452127999995 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm73 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm73 4 1 =
      ∑ n ∈ wMm73, ((6 * n + 4) ^ 2 - 4) *
        ((Cache12800.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm73_r_fast : tableEnergyRadius t wMm73 4 1 = (1416601888595957308929294624782072097314646161113189180307887342471802609288217332811816 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm73 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm73 4 1 =
      ∑ n ∈ wMm73, (|((6 * n + 4) ^ 2 - 4)| * (Cache12800.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache12800.entries[idx n]?.getD (0, 0)).1| +
          (Cache12800.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm73

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm73_c : tableEnergyNumerator t wMm73 4 1 = (125715699375745876596462573691597464873389781595406999544555001233407742090039241512452127999995 : ℤ) := by
  exact KsIndex.NegSignProdFastMm73.eMm73_c_fast
theorem eMm73_r : tableEnergyRadius t wMm73 4 1 = (1416601888595957308929294624782072097314646161113189180307887342471802609288217332811816 : ℤ) := by
  exact KsIndex.NegSignProdFastMm73.eMm73_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm73_c
#print axioms KsIndex.NegSignProd.eMm73_r
