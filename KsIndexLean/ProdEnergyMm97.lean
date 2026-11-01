module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache14336

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm97 : Finset ℤ := Finset.Ioc (-1985) (-1921)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm97

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm97)

def idx (n : ℤ) : ℕ := (n - (-2049)).toNat

lemma mem_wMm97 {n : ℤ} (hn : n ∈ wMm97) : (-1985) < n ∧ n ≤ (-1921) := by
  simpa only [wMm97, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm97) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm97 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm97) :
    2 * Cache14336.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm97 hn
  simp only [idx, Cache14336.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm97) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm97 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm97) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm97 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm97) :
    sampleNumerator (2 * n + 1) =
      (Cache14336.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache14336.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm97) :
    sampleRadius (2 * n + 1) =
      (Cache14336.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache14336.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm97_c_fast : tableEnergyNumerator t wMm97 4 1 = (298864610587779282768095864900131537028270768615127626893120287871092283800296221458980753176422 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm97 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm97 4 1 =
      ∑ n ∈ wMm97, ((6 * n + 4) ^ 2 - 4) *
        ((Cache14336.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm97_r_fast : tableEnergyRadius t wMm97 4 1 = (3990571919220012796220969136857238487091552214042217594941769449032952281581124834529875 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm97 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm97 4 1 =
      ∑ n ∈ wMm97, (|((6 * n + 4) ^ 2 - 4)| * (Cache14336.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache14336.entries[idx n]?.getD (0, 0)).1| +
          (Cache14336.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm97

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm97_c : tableEnergyNumerator t wMm97 4 1 = (298864610587779282768095864900131537028270768615127626893120287871092283800296221458980753176422 : ℤ) := by
  exact KsIndex.NegSignProdFastMm97.eMm97_c_fast
theorem eMm97_r : tableEnergyRadius t wMm97 4 1 = (3990571919220012796220969136857238487091552214042217594941769449032952281581124834529875 : ℤ) := by
  exact KsIndex.NegSignProdFastMm97.eMm97_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm97_c
#print axioms KsIndex.NegSignProd.eMm97_r
