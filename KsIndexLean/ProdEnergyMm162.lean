module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache18432

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm162 : Finset ℤ := Finset.Ioc (2175) (2239)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm162

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm162)

def idx (n : ℤ) : ℕ := (n - (2047)).toNat

lemma mem_wMm162 {n : ℤ} (hn : n ∈ wMm162) : (2175) < n ∧ n ≤ (2239) := by
  simpa only [wMm162, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm162) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm162 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm162) :
    2 * Cache18432.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm162 hn
  simp only [idx, Cache18432.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm162) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm162 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm162) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm162 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm162) :
    sampleNumerator (2 * n + 1) =
      (Cache18432.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache18432.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm162) :
    sampleRadius (2 * n + 1) =
      (Cache18432.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache18432.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm162_c_fast : tableEnergyNumerator t wMm162 4 1 = (3805158393094694499767767704362200257197339108783544248597091948065862422967934326964790455741094 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm162 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm162 4 1 =
      ∑ n ∈ wMm162, ((6 * n + 4) ^ 2 - 4) *
        ((Cache18432.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm162_r_fast : tableEnergyRadius t wMm162 4 1 = (12528783409947694658067141997313347515228889742154679185069145264894156624692204984428051 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm162 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm162 4 1 =
      ∑ n ∈ wMm162, (|((6 * n + 4) ^ 2 - 4)| * (Cache18432.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache18432.entries[idx n]?.getD (0, 0)).1| +
          (Cache18432.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm162

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm162_c : tableEnergyNumerator t wMm162 4 1 = (3805158393094694499767767704362200257197339108783544248597091948065862422967934326964790455741094 : ℤ) := by
  exact KsIndex.NegSignProdFastMm162.eMm162_c_fast
theorem eMm162_r : tableEnergyRadius t wMm162 4 1 = (12528783409947694658067141997313347515228889742154679185069145264894156624692204984428051 : ℤ) := by
  exact KsIndex.NegSignProdFastMm162.eMm162_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm162_c
#print axioms KsIndex.NegSignProd.eMm162_r
