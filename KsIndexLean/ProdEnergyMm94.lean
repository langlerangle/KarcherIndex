module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache14080

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm94 : Finset ℤ := Finset.Ioc (-2177) (-2113)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm94

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm94)

def idx (n : ℤ) : ℕ := (n - (-2305)).toNat

lemma mem_wMm94 {n : ℤ} (hn : n ∈ wMm94) : (-2177) < n ∧ n ≤ (-2113) := by
  simpa only [wMm94, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm94) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm94 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm94) :
    2 * Cache14080.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm94 hn
  simp only [idx, Cache14080.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm94) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm94 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm94) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm94 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm94) :
    sampleNumerator (2 * n + 1) =
      (Cache14080.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache14080.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm94) :
    sampleRadius (2 * n + 1) =
      (Cache14080.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache14080.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm94_c_fast : tableEnergyNumerator t wMm94 4 1 = (260565385308448789541277274832117294196566390862792582020637690099152622004636781765464943208819 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm94 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm94 4 1 =
      ∑ n ∈ wMm94, ((6 * n + 4) ^ 2 - 4) *
        ((Cache14080.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm94_r_fast : tableEnergyRadius t wMm94 4 1 = (3380008996186566044090156409523477093098671288073434408373597278802610649474944938611455 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm94 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm94 4 1 =
      ∑ n ∈ wMm94, (|((6 * n + 4) ^ 2 - 4)| * (Cache14080.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache14080.entries[idx n]?.getD (0, 0)).1| +
          (Cache14080.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm94

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm94_c : tableEnergyNumerator t wMm94 4 1 = (260565385308448789541277274832117294196566390862792582020637690099152622004636781765464943208819 : ℤ) := by
  exact KsIndex.NegSignProdFastMm94.eMm94_c_fast
theorem eMm94_r : tableEnergyRadius t wMm94 4 1 = (3380008996186566044090156409523477093098671288073434408373597278802610649474944938611455 : ℤ) := by
  exact KsIndex.NegSignProdFastMm94.eMm94_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm94_c
#print axioms KsIndex.NegSignProd.eMm94_r
