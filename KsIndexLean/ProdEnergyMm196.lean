module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache20736

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm196 : Finset ℤ := Finset.Ioc (4351) (4415)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm196

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm196)

def idx (n : ℤ) : ℕ := (n - (4351)).toNat

lemma mem_wMm196 {n : ℤ} (hn : n ∈ wMm196) : (4351) < n ∧ n ≤ (4415) := by
  simpa only [wMm196, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm196) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm196 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm196) :
    2 * Cache20736.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm196 hn
  simp only [idx, Cache20736.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm196) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm196 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm196) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm196 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm196) :
    sampleNumerator (2 * n + 1) =
      (Cache20736.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache20736.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm196) :
    sampleRadius (2 * n + 1) =
      (Cache20736.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache20736.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm196_c_fast : tableEnergyNumerator t wMm196 4 1 = (990349616937392677409844289942434446886199265785964546710458065101581954983961525576801160017995 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm196 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm196 4 1 =
      ∑ n ∈ wMm196, ((6 * n + 4) ^ 2 - 4) *
        ((Cache20736.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm196_r_fast : tableEnergyRadius t wMm196 4 1 = (3136932315023390433739644633361849871645981894248184617173966381750153896984220941448137 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm196 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm196 4 1 =
      ∑ n ∈ wMm196, (|((6 * n + 4) ^ 2 - 4)| * (Cache20736.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache20736.entries[idx n]?.getD (0, 0)).1| +
          (Cache20736.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm196

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm196_c : tableEnergyNumerator t wMm196 4 1 = (990349616937392677409844289942434446886199265785964546710458065101581954983961525576801160017995 : ℤ) := by
  exact KsIndex.NegSignProdFastMm196.eMm196_c_fast
theorem eMm196_r : tableEnergyRadius t wMm196 4 1 = (3136932315023390433739644633361849871645981894248184617173966381750153896984220941448137 : ℤ) := by
  exact KsIndex.NegSignProdFastMm196.eMm196_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm196_c
#print axioms KsIndex.NegSignProd.eMm196_r
