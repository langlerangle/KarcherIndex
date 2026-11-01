module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache17664

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm149 : Finset ℤ := Finset.Ioc (1343) (1407)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm149

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm149)

def idx (n : ℤ) : ℕ := (n - (1279)).toNat

lemma mem_wMm149 {n : ℤ} (hn : n ∈ wMm149) : (1343) < n ∧ n ≤ (1407) := by
  simpa only [wMm149, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm149) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm149 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm149) :
    2 * Cache17664.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm149 hn
  simp only [idx, Cache17664.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm149) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm149 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm149) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm149 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm149) :
    sampleNumerator (2 * n + 1) =
      (Cache17664.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache17664.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm149) :
    sampleRadius (2 * n + 1) =
      (Cache17664.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache17664.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm149_c_fast : tableEnergyNumerator t wMm149 4 1 = (9650020083361314435823409533795906210752539807174175731697381473589676735705551626460043446630609 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm149 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm149 4 1 =
      ∑ n ∈ wMm149, ((6 * n + 4) ^ 2 - 4) *
        ((Cache17664.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm149_r_fast : tableEnergyRadius t wMm149 4 1 = (32624375287384570505850334555246042428747021755504660564114984576936380939420288098252078 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm149 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm149 4 1 =
      ∑ n ∈ wMm149, (|((6 * n + 4) ^ 2 - 4)| * (Cache17664.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache17664.entries[idx n]?.getD (0, 0)).1| +
          (Cache17664.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm149

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm149_c : tableEnergyNumerator t wMm149 4 1 = (9650020083361314435823409533795906210752539807174175731697381473589676735705551626460043446630609 : ℤ) := by
  exact KsIndex.NegSignProdFastMm149.eMm149_c_fast
theorem eMm149_r : tableEnergyRadius t wMm149 4 1 = (32624375287384570505850334555246042428747021755504660564114984576936380939420288098252078 : ℤ) := by
  exact KsIndex.NegSignProdFastMm149.eMm149_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm149_c
#print axioms KsIndex.NegSignProd.eMm149_r
