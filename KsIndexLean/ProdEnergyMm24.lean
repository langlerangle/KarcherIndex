module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache9728

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm24 : Finset ℤ := Finset.Ioc (-6657) (-6593)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm24

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm24)

def idx (n : ℤ) : ℕ := (n - (-6657)).toNat

lemma mem_wMm24 {n : ℤ} (hn : n ∈ wMm24) : (-6657) < n ∧ n ≤ (-6593) := by
  simpa only [wMm24, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm24) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm24 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm24) :
    2 * Cache9728.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm24 hn
  simp only [idx, Cache9728.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm24) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm24 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm24) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm24 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm24) :
    sampleNumerator (2 * n + 1) =
      (Cache9728.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache9728.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm24) :
    sampleRadius (2 * n + 1) =
      (Cache9728.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache9728.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm24_c_fast : tableEnergyNumerator t wMm24 4 1 = (46367873802014637364575562035000486348754902530652305461543527813082471407217621275259853882405 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm24 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm24 4 1 =
      ∑ n ∈ wMm24, ((6 * n + 4) ^ 2 - 4) *
        ((Cache9728.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm24_r_fast : tableEnergyRadius t wMm24 4 1 = (442617930619216209503383179879623612856046770403075912568276635008311368361799434645583 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm24 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm24 4 1 =
      ∑ n ∈ wMm24, (|((6 * n + 4) ^ 2 - 4)| * (Cache9728.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache9728.entries[idx n]?.getD (0, 0)).1| +
          (Cache9728.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm24

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm24_c : tableEnergyNumerator t wMm24 4 1 = (46367873802014637364575562035000486348754902530652305461543527813082471407217621275259853882405 : ℤ) := by
  exact KsIndex.NegSignProdFastMm24.eMm24_c_fast
theorem eMm24_r : tableEnergyRadius t wMm24 4 1 = (442617930619216209503383179879623612856046770403075912568276635008311368361799434645583 : ℤ) := by
  exact KsIndex.NegSignProdFastMm24.eMm24_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm24_c
#print axioms KsIndex.NegSignProd.eMm24_r
