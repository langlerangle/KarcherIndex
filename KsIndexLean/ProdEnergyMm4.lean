module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache8448

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm4 : Finset ℤ := Finset.Ioc (-7937) (-7873)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm4

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm4)

def idx (n : ℤ) : ℕ := (n - (-7937)).toNat

lemma mem_wMm4 {n : ℤ} (hn : n ∈ wMm4) : (-7937) < n ∧ n ≤ (-7873) := by
  simpa only [wMm4, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm4) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm4 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm4) :
    2 * Cache8448.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm4 hn
  simp only [idx, Cache8448.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm4) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm4 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm4) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm4 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm4) :
    sampleNumerator (2 * n + 1) =
      (Cache8448.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache8448.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm4) :
    sampleRadius (2 * n + 1) =
      (Cache8448.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache8448.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm4_c_fast : tableEnergyNumerator t wMm4 4 1 = (35016660749835215647371629301251749997098649831494381446694087730584621775920756236273555969477 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm4 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm4 4 1 =
      ∑ n ∈ wMm4, ((6 * n + 4) ^ 2 - 4) *
        ((Cache8448.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm4_r_fast : tableEnergyRadius t wMm4 4 1 = (320374240432115110717556630509606000731066892490179355807218262121444776973847112272767 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm4 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm4 4 1 =
      ∑ n ∈ wMm4, (|((6 * n + 4) ^ 2 - 4)| * (Cache8448.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache8448.entries[idx n]?.getD (0, 0)).1| +
          (Cache8448.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm4

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm4_c : tableEnergyNumerator t wMm4 4 1 = (35016660749835215647371629301251749997098649831494381446694087730584621775920756236273555969477 : ℤ) := by
  exact KsIndex.NegSignProdFastMm4.eMm4_c_fast
theorem eMm4_r : tableEnergyRadius t wMm4 4 1 = (320374240432115110717556630509606000731066892490179355807218262121444776973847112272767 : ℤ) := by
  exact KsIndex.NegSignProdFastMm4.eMm4_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm4_c
#print axioms KsIndex.NegSignProd.eMm4_r
