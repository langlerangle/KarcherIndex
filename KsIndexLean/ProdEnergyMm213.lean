module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache21760

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm213 : Finset ℤ := Finset.Ioc (5439) (5503)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm213

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm213)

def idx (n : ℤ) : ℕ := (n - (5375)).toNat

lemma mem_wMm213 {n : ℤ} (hn : n ∈ wMm213) : (5439) < n ∧ n ≤ (5503) := by
  simpa only [wMm213, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm213) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm213 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm213) :
    2 * Cache21760.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm213 hn
  simp only [idx, Cache21760.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm213) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm213 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm213) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm213 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm213) :
    sampleNumerator (2 * n + 1) =
      (Cache21760.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache21760.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm213) :
    sampleRadius (2 * n + 1) =
      (Cache21760.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache21760.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm213_c_fast : tableEnergyNumerator t wMm213 4 1 = (641532757579762829296466878911777254898744575833232107578791041417369994335156708341779399895148 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm213 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm213 4 1 =
      ∑ n ∈ wMm213, ((6 * n + 4) ^ 2 - 4) *
        ((Cache21760.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm213_r_fast : tableEnergyRadius t wMm213 4 1 = (2006597356123842331445023994610730519234229893056504683264042704586023201853007637338625 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm213 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm213 4 1 =
      ∑ n ∈ wMm213, (|((6 * n + 4) ^ 2 - 4)| * (Cache21760.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache21760.entries[idx n]?.getD (0, 0)).1| +
          (Cache21760.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm213

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm213_c : tableEnergyNumerator t wMm213 4 1 = (641532757579762829296466878911777254898744575833232107578791041417369994335156708341779399895148 : ℤ) := by
  exact KsIndex.NegSignProdFastMm213.eMm213_c_fast
theorem eMm213_r : tableEnergyRadius t wMm213 4 1 = (2006597356123842331445023994610730519234229893056504683264042704586023201853007637338625 : ℤ) := by
  exact KsIndex.NegSignProdFastMm213.eMm213_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm213_c
#print axioms KsIndex.NegSignProd.eMm213_r
