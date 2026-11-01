module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache13312

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm82 : Finset ℤ := Finset.Ioc (-2945) (-2881)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm82

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm82)

def idx (n : ℤ) : ℕ := (n - (-3073)).toNat

lemma mem_wMm82 {n : ℤ} (hn : n ∈ wMm82) : (-2945) < n ∧ n ≤ (-2881) := by
  simpa only [wMm82, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm82) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm82 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm82) :
    2 * Cache13312.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm82 hn
  simp only [idx, Cache13312.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm82) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm82 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm82) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm82 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm82) :
    sampleNumerator (2 * n + 1) =
      (Cache13312.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache13312.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm82) :
    sampleRadius (2 * n + 1) =
      (Cache13312.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache13312.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm82_c_fast : tableEnergyNumerator t wMm82 4 1 = (165260177713200608663553669331788831188548154735632900215120086183344127879095732758308176856013 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm82 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm82 4 1 =
      ∑ n ∈ wMm82, ((6 * n + 4) ^ 2 - 4) *
        ((Cache13312.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm82_r_fast : tableEnergyRadius t wMm82 4 1 = (1958704759175572547390022867148440731922513356678358245380350722637860110567061408109790 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm82 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm82 4 1 =
      ∑ n ∈ wMm82, (|((6 * n + 4) ^ 2 - 4)| * (Cache13312.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache13312.entries[idx n]?.getD (0, 0)).1| +
          (Cache13312.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm82

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm82_c : tableEnergyNumerator t wMm82 4 1 = (165260177713200608663553669331788831188548154735632900215120086183344127879095732758308176856013 : ℤ) := by
  exact KsIndex.NegSignProdFastMm82.eMm82_c_fast
theorem eMm82_r : tableEnergyRadius t wMm82 4 1 = (1958704759175572547390022867148440731922513356678358245380350722637860110567061408109790 : ℤ) := by
  exact KsIndex.NegSignProdFastMm82.eMm82_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm82_c
#print axioms KsIndex.NegSignProd.eMm82_r
