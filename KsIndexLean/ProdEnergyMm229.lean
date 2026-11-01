module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache22784

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm229 : Finset ℤ := Finset.Ioc (6463) (6527)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm229

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm229)

def idx (n : ℤ) : ℕ := (n - (6399)).toNat

lemma mem_wMm229 {n : ℤ} (hn : n ∈ wMm229) : (6463) < n ∧ n ≤ (6527) := by
  simpa only [wMm229, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm229) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm229 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm229) :
    2 * Cache22784.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm229 hn
  simp only [idx, Cache22784.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm229) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm229 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm229) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm229 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm229) :
    sampleNumerator (2 * n + 1) =
      (Cache22784.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache22784.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm229) :
    sampleRadius (2 * n + 1) =
      (Cache22784.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache22784.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm229_c_fast : tableEnergyNumerator t wMm229 4 1 = (458587067635125660413858531422334136802877021388821813168771667779599756857219579741051863370994 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm229 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm229 4 1 =
      ∑ n ∈ wMm229, ((6 * n + 4) ^ 2 - 4) *
        ((Cache22784.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm229_r_fast : tableEnergyRadius t wMm229 4 1 = (1420414080443762714974469334740274309036619736388221552370354514799957470755023852296532 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm229 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm229 4 1 =
      ∑ n ∈ wMm229, (|((6 * n + 4) ^ 2 - 4)| * (Cache22784.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache22784.entries[idx n]?.getD (0, 0)).1| +
          (Cache22784.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm229

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm229_c : tableEnergyNumerator t wMm229 4 1 = (458587067635125660413858531422334136802877021388821813168771667779599756857219579741051863370994 : ℤ) := by
  exact KsIndex.NegSignProdFastMm229.eMm229_c_fast
theorem eMm229_r : tableEnergyRadius t wMm229 4 1 = (1420414080443762714974469334740274309036619736388221552370354514799957470755023852296532 : ℤ) := by
  exact KsIndex.NegSignProdFastMm229.eMm229_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm229_c
#print axioms KsIndex.NegSignProd.eMm229_r
