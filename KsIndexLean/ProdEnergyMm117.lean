module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache15616

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm117 : Finset ℤ := Finset.Ioc (-705) (-641)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm117

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm117)

def idx (n : ℤ) : ℕ := (n - (-769)).toNat

lemma mem_wMm117 {n : ℤ} (hn : n ∈ wMm117) : (-705) < n ∧ n ≤ (-641) := by
  simpa only [wMm117, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm117) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm117 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm117) :
    2 * Cache15616.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm117 hn
  simp only [idx, Cache15616.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm117) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm117 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm117) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm117 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm117) :
    sampleNumerator (2 * n + 1) =
      (Cache15616.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache15616.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm117) :
    sampleRadius (2 * n + 1) =
      (Cache15616.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache15616.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm117_c_fast : tableEnergyNumerator t wMm117 4 1 = (1278738269969922581717575544069377762308984761927237519241796441942364868962083259898236082467177 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm117 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm117 4 1 =
      ∑ n ∈ wMm117, ((6 * n + 4) ^ 2 - 4) *
        ((Cache15616.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm117_r_fast : tableEnergyRadius t wMm117 4 1 = (25062050834969024640291432937361037255862117750432328771019515201960658710301609802831278 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm117 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm117 4 1 =
      ∑ n ∈ wMm117, (|((6 * n + 4) ^ 2 - 4)| * (Cache15616.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache15616.entries[idx n]?.getD (0, 0)).1| +
          (Cache15616.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm117

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm117_c : tableEnergyNumerator t wMm117 4 1 = (1278738269969922581717575544069377762308984761927237519241796441942364868962083259898236082467177 : ℤ) := by
  exact KsIndex.NegSignProdFastMm117.eMm117_c_fast
theorem eMm117_r : tableEnergyRadius t wMm117 4 1 = (25062050834969024640291432937361037255862117750432328771019515201960658710301609802831278 : ℤ) := by
  exact KsIndex.NegSignProdFastMm117.eMm117_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm117_c
#print axioms KsIndex.NegSignProd.eMm117_r
