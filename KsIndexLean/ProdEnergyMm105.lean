module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache14848

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm105 : Finset ℤ := Finset.Ioc (-1473) (-1409)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm105

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm105)

def idx (n : ℤ) : ℕ := (n - (-1537)).toNat

lemma mem_wMm105 {n : ℤ} (hn : n ∈ wMm105) : (-1473) < n ∧ n ≤ (-1409) := by
  simpa only [wMm105, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm105) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm105 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm105) :
    2 * Cache14848.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm105 hn
  simp only [idx, Cache14848.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm105) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm105 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm105) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm105 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm105) :
    sampleNumerator (2 * n + 1) =
      (Cache14848.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache14848.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm105) :
    sampleRadius (2 * n + 1) =
      (Cache14848.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache14848.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm105_c_fast : tableEnergyNumerator t wMm105 4 1 = (462162356903150540264858672358169595096395712113087495821816282296699757630211723673869550528505 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm105 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm105 4 1 =
      ∑ n ∈ wMm105, ((6 * n + 4) ^ 2 - 4) *
        ((Cache14848.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm105_r_fast : tableEnergyRadius t wMm105 4 1 = (6808865562316948853403501602933187373331414702581135815524251930163726995794294405900012 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm105 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm105 4 1 =
      ∑ n ∈ wMm105, (|((6 * n + 4) ^ 2 - 4)| * (Cache14848.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache14848.entries[idx n]?.getD (0, 0)).1| +
          (Cache14848.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm105

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm105_c : tableEnergyNumerator t wMm105 4 1 = (462162356903150540264858672358169595096395712113087495821816282296699757630211723673869550528505 : ℤ) := by
  exact KsIndex.NegSignProdFastMm105.eMm105_c_fast
theorem eMm105_r : tableEnergyRadius t wMm105 4 1 = (6808865562316948853403501602933187373331414702581135815524251930163726995794294405900012 : ℤ) := by
  exact KsIndex.NegSignProdFastMm105.eMm105_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm105_c
#print axioms KsIndex.NegSignProd.eMm105_r
