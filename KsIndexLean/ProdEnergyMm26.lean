module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache9728

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm26 : Finset ℤ := Finset.Ioc (-6529) (-6465)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm26

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm26)

def idx (n : ℤ) : ℕ := (n - (-6657)).toNat

lemma mem_wMm26 {n : ℤ} (hn : n ∈ wMm26) : (-6529) < n ∧ n ≤ (-6465) := by
  simpa only [wMm26, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm26) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm26 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm26) :
    2 * Cache9728.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm26 hn
  simp only [idx, Cache9728.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm26) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm26 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm26) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm26 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm26) :
    sampleNumerator (2 * n + 1) =
      (Cache9728.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache9728.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm26) :
    sampleRadius (2 * n + 1) =
      (Cache9728.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache9728.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm26_c_fast : tableEnergyNumerator t wMm26 4 1 = (47821377201124420840410623386347145647138589333396442338670917403171164476335674116263367223819 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm26 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm26 4 1 =
      ∑ n ∈ wMm26, ((6 * n + 4) ^ 2 - 4) *
        ((Cache9728.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm26_r_fast : tableEnergyRadius t wMm26 4 1 = (458673727880229256723438181635063348021833561090880036791260756166869666166584797091915 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm26 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm26 4 1 =
      ∑ n ∈ wMm26, (|((6 * n + 4) ^ 2 - 4)| * (Cache9728.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache9728.entries[idx n]?.getD (0, 0)).1| +
          (Cache9728.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm26

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm26_c : tableEnergyNumerator t wMm26 4 1 = (47821377201124420840410623386347145647138589333396442338670917403171164476335674116263367223819 : ℤ) := by
  exact KsIndex.NegSignProdFastMm26.eMm26_c_fast
theorem eMm26_r : tableEnergyRadius t wMm26 4 1 = (458673727880229256723438181635063348021833561090880036791260756166869666166584797091915 : ℤ) := by
  exact KsIndex.NegSignProdFastMm26.eMm26_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm26_c
#print axioms KsIndex.NegSignProd.eMm26_r
