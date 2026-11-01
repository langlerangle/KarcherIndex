module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache10752

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm40 : Finset ℤ := Finset.Ioc (-5633) (-5569)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm40

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm40)

def idx (n : ℤ) : ℕ := (n - (-5633)).toNat

lemma mem_wMm40 {n : ℤ} (hn : n ∈ wMm40) : (-5633) < n ∧ n ≤ (-5569) := by
  simpa only [wMm40, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm40) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm40 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm40) :
    2 * Cache10752.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm40 hn
  simp only [idx, Cache10752.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm40) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm40 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm40) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm40 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm40) :
    sampleNumerator (2 * n + 1) =
      (Cache10752.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache10752.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm40) :
    sampleRadius (2 * n + 1) =
      (Cache10752.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache10752.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm40_c_fast : tableEnergyNumerator t wMm40 4 1 = (60415784330147735706086417300156314527479102024197806260351982722333561067838124992742098227612 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm40 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm40 4 1 =
      ∑ n ∈ wMm40, ((6 * n + 4) ^ 2 - 4) *
        ((Cache10752.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm40_r_fast : tableEnergyRadius t wMm40 4 1 = (601189970525407473899719955262482782710081014535726316032201073828612938213955321160552 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm40 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm40 4 1 =
      ∑ n ∈ wMm40, (|((6 * n + 4) ^ 2 - 4)| * (Cache10752.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache10752.entries[idx n]?.getD (0, 0)).1| +
          (Cache10752.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm40

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm40_c : tableEnergyNumerator t wMm40 4 1 = (60415784330147735706086417300156314527479102024197806260351982722333561067838124992742098227612 : ℤ) := by
  exact KsIndex.NegSignProdFastMm40.eMm40_c_fast
theorem eMm40_r : tableEnergyRadius t wMm40 4 1 = (601189970525407473899719955262482782710081014535726316032201073828612938213955321160552 : ℤ) := by
  exact KsIndex.NegSignProdFastMm40.eMm40_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm40_c
#print axioms KsIndex.NegSignProd.eMm40_r
