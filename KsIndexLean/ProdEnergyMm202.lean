module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache20992

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm202 : Finset ℤ := Finset.Ioc (4735) (4799)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm202

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm202)

def idx (n : ℤ) : ℕ := (n - (4607)).toNat

lemma mem_wMm202 {n : ℤ} (hn : n ∈ wMm202) : (4735) < n ∧ n ≤ (4799) := by
  simpa only [wMm202, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm202) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm202 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm202) :
    2 * Cache20992.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm202 hn
  simp only [idx, Cache20992.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm202) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm202 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm202) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm202 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm202) :
    sampleNumerator (2 * n + 1) =
      (Cache20992.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache20992.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm202) :
    sampleRadius (2 * n + 1) =
      (Cache20992.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache20992.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm202_c_fast : tableEnergyNumerator t wMm202 4 1 = (840125351504890421555951639021223736127629445236365451564482366249982400284221951303177138194756 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm202 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm202 4 1 =
      ∑ n ∈ wMm202, ((6 * n + 4) ^ 2 - 4) *
        ((Cache20992.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm202_r_fast : tableEnergyRadius t wMm202 4 1 = (2648432634590030086262545545047845096626202273379547518086609924308989032980555781208488 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm202 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm202 4 1 =
      ∑ n ∈ wMm202, (|((6 * n + 4) ^ 2 - 4)| * (Cache20992.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache20992.entries[idx n]?.getD (0, 0)).1| +
          (Cache20992.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm202

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm202_c : tableEnergyNumerator t wMm202 4 1 = (840125351504890421555951639021223736127629445236365451564482366249982400284221951303177138194756 : ℤ) := by
  exact KsIndex.NegSignProdFastMm202.eMm202_c_fast
theorem eMm202_r : tableEnergyRadius t wMm202 4 1 = (2648432634590030086262545545047845096626202273379547518086609924308989032980555781208488 : ℤ) := by
  exact KsIndex.NegSignProdFastMm202.eMm202_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm202_c
#print axioms KsIndex.NegSignProd.eMm202_r
