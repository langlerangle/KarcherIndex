module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache17920

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm152 : Finset ℤ := Finset.Ioc (1535) (1599)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm152

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm152)

def idx (n : ℤ) : ℕ := (n - (1535)).toNat

lemma mem_wMm152 {n : ℤ} (hn : n ∈ wMm152) : (1535) < n ∧ n ≤ (1599) := by
  simpa only [wMm152, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm152) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm152 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm152) :
    2 * Cache17920.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm152 hn
  simp only [idx, Cache17920.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm152) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm152 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm152) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm152 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm152) :
    sampleNumerator (2 * n + 1) =
      (Cache17920.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache17920.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm152) :
    sampleRadius (2 * n + 1) =
      (Cache17920.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache17920.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm152_c_fast : tableEnergyNumerator t wMm152 4 1 = (7461087260093267836367151650043536681064136290500016649625858409826561437970307394735145350420018 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm152 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm152 4 1 =
      ∑ n ∈ wMm152, ((6 * n + 4) ^ 2 - 4) *
        ((Cache17920.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm152_r_fast : tableEnergyRadius t wMm152 4 1 = (25041254389347051563688063859778374482614714576322230789520920774209253035537748423260007 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm152 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm152 4 1 =
      ∑ n ∈ wMm152, (|((6 * n + 4) ^ 2 - 4)| * (Cache17920.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache17920.entries[idx n]?.getD (0, 0)).1| +
          (Cache17920.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm152

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm152_c : tableEnergyNumerator t wMm152 4 1 = (7461087260093267836367151650043536681064136290500016649625858409826561437970307394735145350420018 : ℤ) := by
  exact KsIndex.NegSignProdFastMm152.eMm152_c_fast
theorem eMm152_r : tableEnergyRadius t wMm152 4 1 = (25041254389347051563688063859778374482614714576322230789520920774209253035537748423260007 : ℤ) := by
  exact KsIndex.NegSignProdFastMm152.eMm152_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm152_c
#print axioms KsIndex.NegSignProd.eMm152_r
