module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache20224

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm189 : Finset ℤ := Finset.Ioc (3903) (3967)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm189

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm189)

def idx (n : ℤ) : ℕ := (n - (3839)).toNat

lemma mem_wMm189 {n : ℤ} (hn : n ∈ wMm189) : (3903) < n ∧ n ≤ (3967) := by
  simpa only [wMm189, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm189) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm189 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm189) :
    2 * Cache20224.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm189 hn
  simp only [idx, Cache20224.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm189) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm189 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm189) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm189 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm189) :
    sampleNumerator (2 * n + 1) =
      (Cache20224.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache20224.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm189) :
    sampleRadius (2 * n + 1) =
      (Cache20224.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache20224.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm189_c_fast : tableEnergyNumerator t wMm189 4 1 = (1223343462377167469824019018938296638892756881118224084758981984102426879967109668674673881005218 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm189 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm189 4 1 =
      ∑ n ∈ wMm189, ((6 * n + 4) ^ 2 - 4) *
        ((Cache20224.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm189_r_fast : tableEnergyRadius t wMm189 4 1 = (3898710487245876284562998196950072812602886130494402155152823975521328630510402613273257 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm189 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm189 4 1 =
      ∑ n ∈ wMm189, (|((6 * n + 4) ^ 2 - 4)| * (Cache20224.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache20224.entries[idx n]?.getD (0, 0)).1| +
          (Cache20224.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm189

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm189_c : tableEnergyNumerator t wMm189 4 1 = (1223343462377167469824019018938296638892756881118224084758981984102426879967109668674673881005218 : ℤ) := by
  exact KsIndex.NegSignProdFastMm189.eMm189_c_fast
theorem eMm189_r : tableEnergyRadius t wMm189 4 1 = (3898710487245876284562998196950072812602886130494402155152823975521328630510402613273257 : ℤ) := by
  exact KsIndex.NegSignProdFastMm189.eMm189_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm189_c
#print axioms KsIndex.NegSignProd.eMm189_r
