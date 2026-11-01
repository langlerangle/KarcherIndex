module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache24320

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm254 : Finset ℤ := Finset.Ioc (8063) (8127)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm254

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm254)

def idx (n : ℤ) : ℕ := (n - (7935)).toNat

lemma mem_wMm254 {n : ℤ} (hn : n ∈ wMm254) : (8063) < n ∧ n ≤ (8127) := by
  simpa only [wMm254, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm254) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm254 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm254) :
    2 * Cache24320.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm254 hn
  simp only [idx, Cache24320.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm254) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm254 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm254) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm254 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm254) :
    sampleNumerator (2 * n + 1) =
      (Cache24320.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache24320.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm254) :
    sampleRadius (2 * n + 1) =
      (Cache24320.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache24320.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm254_c_fast : tableEnergyNumerator t wMm254 4 1 = (298152038960138676214441851015748617822306876985151468006459972900998125880732560975646784955017 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm254 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm254 4 1 =
      ∑ n ∈ wMm254, ((6 * n + 4) ^ 2 - 4) *
        ((Cache24320.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm254_r_fast : tableEnergyRadius t wMm254 4 1 = (911937104033607768862886911422009353297482665005548709884484008130929741245118809654292 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm254 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm254 4 1 =
      ∑ n ∈ wMm254, (|((6 * n + 4) ^ 2 - 4)| * (Cache24320.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache24320.entries[idx n]?.getD (0, 0)).1| +
          (Cache24320.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm254

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm254_c : tableEnergyNumerator t wMm254 4 1 = (298152038960138676214441851015748617822306876985151468006459972900998125880732560975646784955017 : ℤ) := by
  exact KsIndex.NegSignProdFastMm254.eMm254_c_fast
theorem eMm254_r : tableEnergyRadius t wMm254 4 1 = (911937104033607768862886911422009353297482665005548709884484008130929741245118809654292 : ℤ) := by
  exact KsIndex.NegSignProdFastMm254.eMm254_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm254_c
#print axioms KsIndex.NegSignProd.eMm254_r
