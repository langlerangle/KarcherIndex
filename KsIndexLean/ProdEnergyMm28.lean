module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache9984

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm28 : Finset ℤ := Finset.Ioc (-6401) (-6337)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm28

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm28)

def idx (n : ℤ) : ℕ := (n - (-6401)).toNat

lemma mem_wMm28 {n : ℤ} (hn : n ∈ wMm28) : (-6401) < n ∧ n ≤ (-6337) := by
  simpa only [wMm28, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm28) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm28 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm28) :
    2 * Cache9984.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm28 hn
  simp only [idx, Cache9984.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm28) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm28 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm28) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm28 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm28) :
    sampleNumerator (2 * n + 1) =
      (Cache9984.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache9984.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm28) :
    sampleRadius (2 * n + 1) =
      (Cache9984.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache9984.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm28_c_fast : tableEnergyNumerator t wMm28 4 1 = (49349229112574028040978370118045116804792378194526437026857652565998885754170194738557873283507 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm28 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm28 4 1 =
      ∑ n ∈ wMm28, ((6 * n + 4) ^ 2 - 4) *
        ((Cache9984.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm28_r_fast : tableEnergyRadius t wMm28 4 1 = (475642427073161434108504969572580012469811289549543403000579807318354545393913474878636 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm28 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm28 4 1 =
      ∑ n ∈ wMm28, (|((6 * n + 4) ^ 2 - 4)| * (Cache9984.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache9984.entries[idx n]?.getD (0, 0)).1| +
          (Cache9984.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm28

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm28_c : tableEnergyNumerator t wMm28 4 1 = (49349229112574028040978370118045116804792378194526437026857652565998885754170194738557873283507 : ℤ) := by
  exact KsIndex.NegSignProdFastMm28.eMm28_c_fast
theorem eMm28_r : tableEnergyRadius t wMm28 4 1 = (475642427073161434108504969572580012469811289549543403000579807318354545393913474878636 : ℤ) := by
  exact KsIndex.NegSignProdFastMm28.eMm28_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm28_c
#print axioms KsIndex.NegSignProd.eMm28_r
