module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache23296

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm236 : Finset ℤ := Finset.Ioc (6911) (6975)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm236

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm236)

def idx (n : ℤ) : ℕ := (n - (6911)).toNat

lemma mem_wMm236 {n : ℤ} (hn : n ∈ wMm236) : (6911) < n ∧ n ≤ (6975) := by
  simpa only [wMm236, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm236) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm236 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm236) :
    2 * Cache23296.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm236 hn
  simp only [idx, Cache23296.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm236) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm236 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm236) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm236 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm236) :
    sampleNumerator (2 * n + 1) =
      (Cache23296.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache23296.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm236) :
    sampleRadius (2 * n + 1) =
      (Cache23296.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache23296.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm236_c_fast : tableEnergyNumerator t wMm236 4 1 = (402501990776691702320804689906329506342686561425654102948819468011386657583278243653417839835044 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm236 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm236 4 1 =
      ∑ n ∈ wMm236, ((6 * n + 4) ^ 2 - 4) *
        ((Cache23296.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm236_r_fast : tableEnergyRadius t wMm236 4 1 = (1241958516211320577054859040743525844156003310386394363769287184803562680074282910475438 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm236 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm236 4 1 =
      ∑ n ∈ wMm236, (|((6 * n + 4) ^ 2 - 4)| * (Cache23296.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache23296.entries[idx n]?.getD (0, 0)).1| +
          (Cache23296.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm236

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm236_c : tableEnergyNumerator t wMm236 4 1 = (402501990776691702320804689906329506342686561425654102948819468011386657583278243653417839835044 : ℤ) := by
  exact KsIndex.NegSignProdFastMm236.eMm236_c_fast
theorem eMm236_r : tableEnergyRadius t wMm236 4 1 = (1241958516211320577054859040743525844156003310386394363769287184803562680074282910475438 : ℤ) := by
  exact KsIndex.NegSignProdFastMm236.eMm236_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm236_c
#print axioms KsIndex.NegSignProd.eMm236_r
