module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache15360

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm114 : Finset ℤ := Finset.Ioc (-897) (-833)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm114

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm114)

def idx (n : ℤ) : ℕ := (n - (-1025)).toNat

lemma mem_wMm114 {n : ℤ} (hn : n ∈ wMm114) : (-897) < n ∧ n ≤ (-833) := by
  simpa only [wMm114, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm114) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm114 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm114) :
    2 * Cache15360.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm114 hn
  simp only [idx, Cache15360.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm114) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm114 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm114) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm114 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm114) :
    sampleNumerator (2 * n + 1) =
      (Cache15360.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache15360.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm114) :
    sampleRadius (2 * n + 1) =
      (Cache15360.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache15360.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm114_c_fast : tableEnergyNumerator t wMm114 4 1 = (926976704616813446374556532980176570927143883924965818423952166782961286072053319722538957021609 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm114 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm114 4 1 =
      ∑ n ∈ wMm114, ((6 * n + 4) ^ 2 - 4) *
        ((Cache15360.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm114_r_fast : tableEnergyRadius t wMm114 4 1 = (16416063370344487253328227248339596155631474450703299200818963658952299777371414119825197 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm114 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm114 4 1 =
      ∑ n ∈ wMm114, (|((6 * n + 4) ^ 2 - 4)| * (Cache15360.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache15360.entries[idx n]?.getD (0, 0)).1| +
          (Cache15360.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm114

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm114_c : tableEnergyNumerator t wMm114 4 1 = (926976704616813446374556532980176570927143883924965818423952166782961286072053319722538957021609 : ℤ) := by
  exact KsIndex.NegSignProdFastMm114.eMm114_c_fast
theorem eMm114_r : tableEnergyRadius t wMm114 4 1 = (16416063370344487253328227248339596155631474450703299200818963658952299777371414119825197 : ℤ) := by
  exact KsIndex.NegSignProdFastMm114.eMm114_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm114_c
#print axioms KsIndex.NegSignProd.eMm114_r
