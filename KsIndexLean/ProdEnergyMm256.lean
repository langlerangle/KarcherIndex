module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache24576

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm256 : Finset ℤ := Finset.Ioc (8191) (8192)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm256

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm256)

def idx (n : ℤ) : ℕ := (n - (8191)).toNat

lemma mem_wMm256 {n : ℤ} (hn : n ∈ wMm256) : (8191) < n ∧ n ≤ (8192) := by
  simpa only [wMm256, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm256) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm256 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm256) :
    2 * Cache24576.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm256 hn
  simp only [idx, Cache24576.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm256) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm256 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm256) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm256 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm256) :
    sampleNumerator (2 * n + 1) =
      (Cache24576.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache24576.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm256) :
    sampleRadius (2 * n + 1) =
      (Cache24576.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache24576.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm256_c_fast : tableEnergyNumerator t wMm256 4 1 = (4551912544007046175893695420693273580703831446848931696779773871296672035610030343512892431273 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm256 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm256 4 1 =
      ∑ n ∈ wMm256, ((6 * n + 4) ^ 2 - 4) *
        ((Cache24576.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm256_r_fast : tableEnergyRadius t wMm256 4 1 = (13913172016287343095862781922824905254993178437272734553102458775372980826157735473512 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm256 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm256 4 1 =
      ∑ n ∈ wMm256, (|((6 * n + 4) ^ 2 - 4)| * (Cache24576.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache24576.entries[idx n]?.getD (0, 0)).1| +
          (Cache24576.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm256

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm256_c : tableEnergyNumerator t wMm256 4 1 = (4551912544007046175893695420693273580703831446848931696779773871296672035610030343512892431273 : ℤ) := by
  exact KsIndex.NegSignProdFastMm256.eMm256_c_fast
theorem eMm256_r : tableEnergyRadius t wMm256 4 1 = (13913172016287343095862781922824905254993178437272734553102458775372980826157735473512 : ℤ) := by
  exact KsIndex.NegSignProdFastMm256.eMm256_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm256_c
#print axioms KsIndex.NegSignProd.eMm256_r
