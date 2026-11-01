module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache23040

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm234 : Finset ℤ := Finset.Ioc (6783) (6847)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm234

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm234)

def idx (n : ℤ) : ℕ := (n - (6655)).toNat

lemma mem_wMm234 {n : ℤ} (hn : n ∈ wMm234) : (6783) < n ∧ n ≤ (6847) := by
  simpa only [wMm234, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm234) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm234 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm234) :
    2 * Cache23040.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm234 hn
  simp only [idx, Cache23040.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm234) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm234 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm234) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm234 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm234) :
    sampleNumerator (2 * n + 1) =
      (Cache23040.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache23040.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm234) :
    sampleRadius (2 * n + 1) =
      (Cache23040.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache23040.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm234_c_fast : tableEnergyNumerator t wMm234 4 1 = (417418209628596162449111068572545357545771364909484340960339073862938933954438619612124178524819 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm234 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm234 4 1 =
      ∑ n ∈ wMm234, ((6 * n + 4) ^ 2 - 4) *
        ((Cache23040.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm234_r_fast : tableEnergyRadius t wMm234 4 1 = (1289353601890479972457607240485428894084042610818243834496711574621493690473180370339068 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm234 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm234 4 1 =
      ∑ n ∈ wMm234, (|((6 * n + 4) ^ 2 - 4)| * (Cache23040.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache23040.entries[idx n]?.getD (0, 0)).1| +
          (Cache23040.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm234

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm234_c : tableEnergyNumerator t wMm234 4 1 = (417418209628596162449111068572545357545771364909484340960339073862938933954438619612124178524819 : ℤ) := by
  exact KsIndex.NegSignProdFastMm234.eMm234_c_fast
theorem eMm234_r : tableEnergyRadius t wMm234 4 1 = (1289353601890479972457607240485428894084042610818243834496711574621493690473180370339068 : ℤ) := by
  exact KsIndex.NegSignProdFastMm234.eMm234_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm234_c
#print axioms KsIndex.NegSignProd.eMm234_r
