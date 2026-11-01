module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache17664

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm150 : Finset ℤ := Finset.Ioc (1407) (1471)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm150

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm150)

def idx (n : ℤ) : ℕ := (n - (1279)).toNat

lemma mem_wMm150 {n : ℤ} (hn : n ∈ wMm150) : (1407) < n ∧ n ≤ (1471) := by
  simpa only [wMm150, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm150) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm150 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm150) :
    2 * Cache17664.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm150 hn
  simp only [idx, Cache17664.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm150) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm150 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm150) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm150 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm150) :
    sampleNumerator (2 * n + 1) =
      (Cache17664.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache17664.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm150) :
    sampleRadius (2 * n + 1) =
      (Cache17664.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache17664.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm150_c_fast : tableEnergyNumerator t wMm150 4 1 = (8823345660678256827818690726814073293838754164839137003956216587664433384224481623614944956730706 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm150 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm150 4 1 =
      ∑ n ∈ wMm150, ((6 * n + 4) ^ 2 - 4) *
        ((Cache17664.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm150_r_fast : tableEnergyRadius t wMm150 4 1 = (29754203171861318078721334410585139382573933069059651004842371196779078498344471161138453 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm150 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm150 4 1 =
      ∑ n ∈ wMm150, (|((6 * n + 4) ^ 2 - 4)| * (Cache17664.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache17664.entries[idx n]?.getD (0, 0)).1| +
          (Cache17664.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm150

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm150_c : tableEnergyNumerator t wMm150 4 1 = (8823345660678256827818690726814073293838754164839137003956216587664433384224481623614944956730706 : ℤ) := by
  exact KsIndex.NegSignProdFastMm150.eMm150_c_fast
theorem eMm150_r : tableEnergyRadius t wMm150 4 1 = (29754203171861318078721334410585139382573933069059651004842371196779078498344471161138453 : ℤ) := by
  exact KsIndex.NegSignProdFastMm150.eMm150_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm150_c
#print axioms KsIndex.NegSignProd.eMm150_r
