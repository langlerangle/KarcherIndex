module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache23040

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm233 : Finset ℤ := Finset.Ioc (6719) (6783)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm233

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm233)

def idx (n : ℤ) : ℕ := (n - (6655)).toNat

lemma mem_wMm233 {n : ℤ} (hn : n ∈ wMm233) : (6719) < n ∧ n ≤ (6783) := by
  simpa only [wMm233, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm233) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm233 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm233) :
    2 * Cache23040.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm233 hn
  simp only [idx, Cache23040.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm233) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm233 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm233) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm233 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm233) :
    sampleNumerator (2 * n + 1) =
      (Cache23040.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache23040.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm233) :
    sampleRadius (2 * n + 1) =
      (Cache23040.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache23040.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm233_c_fast : tableEnergyNumerator t wMm233 4 1 = (425192099009815312919029496116784235274970025234449741843274244861353517205670484520792412033611 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm233 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm233 4 1 =
      ∑ n ∈ wMm233, ((6 * n + 4) ^ 2 - 4) *
        ((Cache23040.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm233_r_fast : tableEnergyRadius t wMm233 4 1 = (1314074078829968569907272535310731111016629382215768394460412352394651865670242947486392 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm233 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm233 4 1 =
      ∑ n ∈ wMm233, (|((6 * n + 4) ^ 2 - 4)| * (Cache23040.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache23040.entries[idx n]?.getD (0, 0)).1| +
          (Cache23040.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm233

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm233_c : tableEnergyNumerator t wMm233 4 1 = (425192099009815312919029496116784235274970025234449741843274244861353517205670484520792412033611 : ℤ) := by
  exact KsIndex.NegSignProdFastMm233.eMm233_c_fast
theorem eMm233_r : tableEnergyRadius t wMm233 4 1 = (1314074078829968569907272535310731111016629382215768394460412352394651865670242947486392 : ℤ) := by
  exact KsIndex.NegSignProdFastMm233.eMm233_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm233_c
#print axioms KsIndex.NegSignProd.eMm233_r
