module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache19968

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm186 : Finset ℤ := Finset.Ioc (3711) (3775)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm186

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm186)

def idx (n : ℤ) : ℕ := (n - (3583)).toNat

lemma mem_wMm186 {n : ℤ} (hn : n ∈ wMm186) : (3711) < n ∧ n ≤ (3775) := by
  simpa only [wMm186, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm186) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm186 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm186) :
    2 * Cache19968.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm186 hn
  simp only [idx, Cache19968.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm186) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm186 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm186) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm186 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm186) :
    sampleNumerator (2 * n + 1) =
      (Cache19968.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache19968.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm186) :
    sampleRadius (2 * n + 1) =
      (Cache19968.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache19968.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm186_c_fast : tableEnergyNumerator t wMm186 4 1 = (1349377443531785173368475803090168049190785296057137203781537978732513346982300812426776305025195 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm186 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm186 4 1 =
      ∑ n ∈ wMm186, ((6 * n + 4) ^ 2 - 4) *
        ((Cache19968.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm186_r_fast : tableEnergyRadius t wMm186 4 1 = (4312575605013344913531425685920148265138927485564437669269012939526328538049202276083687 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm186 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm186 4 1 =
      ∑ n ∈ wMm186, (|((6 * n + 4) ^ 2 - 4)| * (Cache19968.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache19968.entries[idx n]?.getD (0, 0)).1| +
          (Cache19968.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm186

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm186_c : tableEnergyNumerator t wMm186 4 1 = (1349377443531785173368475803090168049190785296057137203781537978732513346982300812426776305025195 : ℤ) := by
  exact KsIndex.NegSignProdFastMm186.eMm186_c_fast
theorem eMm186_r : tableEnergyRadius t wMm186 4 1 = (4312575605013344913531425685920148265138927485564437669269012939526328538049202276083687 : ℤ) := by
  exact KsIndex.NegSignProdFastMm186.eMm186_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm186_c
#print axioms KsIndex.NegSignProd.eMm186_r
