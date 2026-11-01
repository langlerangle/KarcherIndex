module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache11520

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm53 : Finset ℤ := Finset.Ioc (-4801) (-4737)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm53

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm53)

def idx (n : ℤ) : ℕ := (n - (-4865)).toNat

lemma mem_wMm53 {n : ℤ} (hn : n ∈ wMm53) : (-4801) < n ∧ n ≤ (-4737) := by
  simpa only [wMm53, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm53) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm53 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm53) :
    2 * Cache11520.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm53 hn
  simp only [idx, Cache11520.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm53) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm53 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm53) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm53 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm53) :
    sampleNumerator (2 * n + 1) =
      (Cache11520.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache11520.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm53) :
    sampleRadius (2 * n + 1) =
      (Cache11520.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache11520.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm53_c_fast : tableEnergyNumerator t wMm53 4 1 = (77672738133012493397405560857880402598908054653526886068656659477903911198647241411016053073481 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm53 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm53 4 1 =
      ∑ n ∈ wMm53, ((6 * n + 4) ^ 2 - 4) *
        ((Cache11520.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm53_r_fast : tableEnergyRadius t wMm53 4 1 = (805259403234268878730047351288268307598617875672870318564971282640841123708404764604827 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm53 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm53 4 1 =
      ∑ n ∈ wMm53, (|((6 * n + 4) ^ 2 - 4)| * (Cache11520.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache11520.entries[idx n]?.getD (0, 0)).1| +
          (Cache11520.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm53

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm53_c : tableEnergyNumerator t wMm53 4 1 = (77672738133012493397405560857880402598908054653526886068656659477903911198647241411016053073481 : ℤ) := by
  exact KsIndex.NegSignProdFastMm53.eMm53_c_fast
theorem eMm53_r : tableEnergyRadius t wMm53 4 1 = (805259403234268878730047351288268307598617875672870318564971282640841123708404764604827 : ℤ) := by
  exact KsIndex.NegSignProdFastMm53.eMm53_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm53_c
#print axioms KsIndex.NegSignProd.eMm53_r
