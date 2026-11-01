module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache13312

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm81 : Finset ℤ := Finset.Ioc (-3009) (-2945)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm81

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm81)

def idx (n : ℤ) : ℕ := (n - (-3073)).toNat

lemma mem_wMm81 {n : ℤ} (hn : n ∈ wMm81) : (-3009) < n ∧ n ≤ (-2945) := by
  simpa only [wMm81, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm81) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm81 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm81) :
    2 * Cache13312.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm81 hn
  simp only [idx, Cache13312.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm81) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm81 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm81) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm81 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm81) :
    sampleNumerator (2 * n + 1) =
      (Cache13312.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache13312.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm81) :
    sampleRadius (2 * n + 1) =
      (Cache13312.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache13312.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm81_c_fast : tableEnergyNumerator t wMm81 4 1 = (159934872798330250138550838544418900805814824424130326814958844166142442249030094995366754515800 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm81 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm81 4 1 =
      ∑ n ∈ wMm81, ((6 * n + 4) ^ 2 - 4) *
        ((Cache13312.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm81_r_fast : tableEnergyRadius t wMm81 4 1 = (1883898289090377524725202946867823282123519488085967406368325556246249561636242923091521 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm81 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm81 4 1 =
      ∑ n ∈ wMm81, (|((6 * n + 4) ^ 2 - 4)| * (Cache13312.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache13312.entries[idx n]?.getD (0, 0)).1| +
          (Cache13312.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm81

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm81_c : tableEnergyNumerator t wMm81 4 1 = (159934872798330250138550838544418900805814824424130326814958844166142442249030094995366754515800 : ℤ) := by
  exact KsIndex.NegSignProdFastMm81.eMm81_c_fast
theorem eMm81_r : tableEnergyRadius t wMm81 4 1 = (1883898289090377524725202946867823282123519488085967406368325556246249561636242923091521 : ℤ) := by
  exact KsIndex.NegSignProdFastMm81.eMm81_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm81_c
#print axioms KsIndex.NegSignProd.eMm81_r
