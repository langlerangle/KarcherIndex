module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache16896

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm136 : Finset ℤ := Finset.Ioc (511) (575)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm136

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm136)

def idx (n : ℤ) : ℕ := (n - (511)).toNat

lemma mem_wMm136 {n : ℤ} (hn : n ∈ wMm136) : (511) < n ∧ n ≤ (575) := by
  simpa only [wMm136, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm136) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm136 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm136) :
    2 * Cache16896.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm136 hn
  simp only [idx, Cache16896.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm136) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm136 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm136) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm136 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm136) :
    sampleNumerator (2 * n + 1) =
      (Cache16896.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache16896.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm136) :
    sampleRadius (2 * n + 1) =
      (Cache16896.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache16896.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm136_c_fast : tableEnergyNumerator t wMm136 4 1 = (60385874023432970491968449537802520855333874587652017910933195290191196536687981120385450543603363 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm136 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm136 4 1 =
      ∑ n ∈ wMm136, ((6 * n + 4) ^ 2 - 4) *
        ((Cache16896.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm136_r_fast : tableEnergyRadius t wMm136 4 1 = (214876445483626316154585951183163166303957969206536792043970600579041318645142255524352276 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm136 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm136 4 1 =
      ∑ n ∈ wMm136, (|((6 * n + 4) ^ 2 - 4)| * (Cache16896.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache16896.entries[idx n]?.getD (0, 0)).1| +
          (Cache16896.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm136

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm136_c : tableEnergyNumerator t wMm136 4 1 = (60385874023432970491968449537802520855333874587652017910933195290191196536687981120385450543603363 : ℤ) := by
  exact KsIndex.NegSignProdFastMm136.eMm136_c_fast
theorem eMm136_r : tableEnergyRadius t wMm136 4 1 = (214876445483626316154585951183163166303957969206536792043970600579041318645142255524352276 : ℤ) := by
  exact KsIndex.NegSignProdFastMm136.eMm136_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm136_c
#print axioms KsIndex.NegSignProd.eMm136_r
