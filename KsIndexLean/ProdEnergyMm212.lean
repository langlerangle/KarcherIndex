module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache21760

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm212 : Finset ℤ := Finset.Ioc (5375) (5439)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm212

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm212)

def idx (n : ℤ) : ℕ := (n - (5375)).toNat

lemma mem_wMm212 {n : ℤ} (hn : n ∈ wMm212) : (5375) < n ∧ n ≤ (5439) := by
  simpa only [wMm212, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm212) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm212 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm212) :
    2 * Cache21760.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm212 hn
  simp only [idx, Cache21760.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm212) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm212 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm212) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm212 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm212) :
    sampleNumerator (2 * n + 1) =
      (Cache21760.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache21760.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm212) :
    sampleRadius (2 * n + 1) =
      (Cache21760.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache21760.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm212_c_fast : tableEnergyNumerator t wMm212 4 1 = (656480561585719076690431992753695675811519297667888125166965859827714683269881392788754800390285 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm212 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm212 4 1 =
      ∑ n ∈ wMm212, ((6 * n + 4) ^ 2 - 4) *
        ((Cache21760.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm212_r_fast : tableEnergyRadius t wMm212 4 1 = (2054727680847070523067829285860708948676126864731268456224690900410870656151868585254027 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm212 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm212 4 1 =
      ∑ n ∈ wMm212, (|((6 * n + 4) ^ 2 - 4)| * (Cache21760.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache21760.entries[idx n]?.getD (0, 0)).1| +
          (Cache21760.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm212

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm212_c : tableEnergyNumerator t wMm212 4 1 = (656480561585719076690431992753695675811519297667888125166965859827714683269881392788754800390285 : ℤ) := by
  exact KsIndex.NegSignProdFastMm212.eMm212_c_fast
theorem eMm212_r : tableEnergyRadius t wMm212 4 1 = (2054727680847070523067829285860708948676126864731268456224690900410870656151868585254027 : ℤ) := by
  exact KsIndex.NegSignProdFastMm212.eMm212_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm212_c
#print axioms KsIndex.NegSignProd.eMm212_r
