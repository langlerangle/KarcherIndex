module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache8448

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm6 : Finset ℤ := Finset.Ioc (-7809) (-7745)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm6

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm6)

def idx (n : ℤ) : ℕ := (n - (-7937)).toNat

lemma mem_wMm6 {n : ℤ} (hn : n ∈ wMm6) : (-7809) < n ∧ n ≤ (-7745) := by
  simpa only [wMm6, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm6) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm6 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm6) :
    2 * Cache8448.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm6 hn
  simp only [idx, Cache8448.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm6) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm6 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm6) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm6 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm6) :
    sampleNumerator (2 * n + 1) =
      (Cache8448.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache8448.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm6) :
    sampleRadius (2 * n + 1) =
      (Cache8448.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache8448.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm6_c_fast : tableEnergyNumerator t wMm6 4 1 = (35940683846344251448016215918750949469294112998696937098047389359917402071809242010185506802567 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm6 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm6 4 1 =
      ∑ n ∈ wMm6, ((6 * n + 4) ^ 2 - 4) *
        ((Cache8448.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm6_r_fast : tableEnergyRadius t wMm6 4 1 = (330102810313665973834939854225328398992333784806729990754989432047437266813557469666922 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm6 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm6 4 1 =
      ∑ n ∈ wMm6, (|((6 * n + 4) ^ 2 - 4)| * (Cache8448.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache8448.entries[idx n]?.getD (0, 0)).1| +
          (Cache8448.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm6

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm6_c : tableEnergyNumerator t wMm6 4 1 = (35940683846344251448016215918750949469294112998696937098047389359917402071809242010185506802567 : ℤ) := by
  exact KsIndex.NegSignProdFastMm6.eMm6_c_fast
theorem eMm6_r : tableEnergyRadius t wMm6 4 1 = (330102810313665973834939854225328398992333784806729990754989432047437266813557469666922 : ℤ) := by
  exact KsIndex.NegSignProdFastMm6.eMm6_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm6_c
#print axioms KsIndex.NegSignProd.eMm6_r
