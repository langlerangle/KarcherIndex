module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache22272

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm221 : Finset ℤ := Finset.Ioc (5951) (6015)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm221

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm221)

def idx (n : ℤ) : ℕ := (n - (5887)).toNat

lemma mem_wMm221 {n : ℤ} (hn : n ∈ wMm221) : (5951) < n ∧ n ≤ (6015) := by
  simpa only [wMm221, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm221) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm221 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm221) :
    2 * Cache22272.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm221 hn
  simp only [idx, Cache22272.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm221) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm221 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm221) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm221 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm221) :
    sampleNumerator (2 * n + 1) =
      (Cache22272.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache22272.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm221) :
    sampleRadius (2 * n + 1) =
      (Cache22272.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache22272.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm221_c_fast : tableEnergyNumerator t wMm221 4 1 = (538498704294386164732333028594043873664439988797491362296059659030909896290063315147740126944439 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm221 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm221 4 1 =
      ∑ n ∈ wMm221, ((6 * n + 4) ^ 2 - 4) *
        ((Cache22272.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm221_r_fast : tableEnergyRadius t wMm221 4 1 = (1675761262430565325710912746525611674285422736060170256426490116076683292912332362151327 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm221 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm221 4 1 =
      ∑ n ∈ wMm221, (|((6 * n + 4) ^ 2 - 4)| * (Cache22272.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache22272.entries[idx n]?.getD (0, 0)).1| +
          (Cache22272.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm221

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm221_c : tableEnergyNumerator t wMm221 4 1 = (538498704294386164732333028594043873664439988797491362296059659030909896290063315147740126944439 : ℤ) := by
  exact KsIndex.NegSignProdFastMm221.eMm221_c_fast
theorem eMm221_r : tableEnergyRadius t wMm221 4 1 = (1675761262430565325710912746525611674285422736060170256426490116076683292912332362151327 : ℤ) := by
  exact KsIndex.NegSignProdFastMm221.eMm221_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm221_c
#print axioms KsIndex.NegSignProd.eMm221_r
