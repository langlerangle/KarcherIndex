module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache8960

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm14 : Finset ℤ := Finset.Ioc (-7297) (-7233)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm14

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm14)

def idx (n : ℤ) : ℕ := (n - (-7425)).toNat

lemma mem_wMm14 {n : ℤ} (hn : n ∈ wMm14) : (-7297) < n ∧ n ≤ (-7233) := by
  simpa only [wMm14, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm14) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm14 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm14) :
    2 * Cache8960.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm14 hn
  simp only [idx, Cache8960.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm14) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm14 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm14) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm14 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm14) :
    sampleNumerator (2 * n + 1) =
      (Cache8960.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache8960.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm14) :
    sampleRadius (2 * n + 1) =
      (Cache8960.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache8960.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm14_c_fast : tableEnergyNumerator t wMm14 4 1 = (40057473115433050649163379772294789436815075131570495245330121962183514161974836254031980707218 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm14 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm14 4 1 =
      ∑ n ∈ wMm14, ((6 * n + 4) ^ 2 - 4) *
        ((Cache8960.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm14_r_fast : tableEnergyRadius t wMm14 4 1 = (373942808625939394022442088325205758888061341180242637871282894837878868470788068369722 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm14 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm14 4 1 =
      ∑ n ∈ wMm14, (|((6 * n + 4) ^ 2 - 4)| * (Cache8960.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache8960.entries[idx n]?.getD (0, 0)).1| +
          (Cache8960.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm14

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm14_c : tableEnergyNumerator t wMm14 4 1 = (40057473115433050649163379772294789436815075131570495245330121962183514161974836254031980707218 : ℤ) := by
  exact KsIndex.NegSignProdFastMm14.eMm14_c_fast
theorem eMm14_r : tableEnergyRadius t wMm14 4 1 = (373942808625939394022442088325205758888061341180242637871282894837878868470788068369722 : ℤ) := by
  exact KsIndex.NegSignProdFastMm14.eMm14_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm14_c
#print axioms KsIndex.NegSignProd.eMm14_r
