module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache12800

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm72 : Finset ℤ := Finset.Ioc (-3585) (-3521)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm72

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm72)

def idx (n : ℤ) : ℕ := (n - (-3585)).toNat

lemma mem_wMm72 {n : ℤ} (hn : n ∈ wMm72) : (-3585) < n ∧ n ≤ (-3521) := by
  simpa only [wMm72, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm72) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm72 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm72) :
    2 * Cache12800.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm72 hn
  simp only [idx, Cache12800.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm72) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm72 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm72) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm72 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm72) :
    sampleNumerator (2 * n + 1) =
      (Cache12800.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache12800.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm72) :
    sampleRadius (2 * n + 1) =
      (Cache12800.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache12800.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm72_c_fast : tableEnergyNumerator t wMm72 4 1 = (122275772868081333118601704991288725014008925795110606018325124891887700263408791456865876170750 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm72 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm72 4 1 =
      ∑ n ∈ wMm72, ((6 * n + 4) ^ 2 - 4) *
        ((Cache12800.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm72_r_fast : tableEnergyRadius t wMm72 4 1 = (1370984550610992074673036796373987125540788880975787367602151789686521499251562244976504 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm72 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm72 4 1 =
      ∑ n ∈ wMm72, (|((6 * n + 4) ^ 2 - 4)| * (Cache12800.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache12800.entries[idx n]?.getD (0, 0)).1| +
          (Cache12800.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm72

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm72_c : tableEnergyNumerator t wMm72 4 1 = (122275772868081333118601704991288725014008925795110606018325124891887700263408791456865876170750 : ℤ) := by
  exact KsIndex.NegSignProdFastMm72.eMm72_c_fast
theorem eMm72_r : tableEnergyRadius t wMm72 4 1 = (1370984550610992074673036796373987125540788880975787367602151789686521499251562244976504 : ℤ) := by
  exact KsIndex.NegSignProdFastMm72.eMm72_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm72_c
#print axioms KsIndex.NegSignProd.eMm72_r
