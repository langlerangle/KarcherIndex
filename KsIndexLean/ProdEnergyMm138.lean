module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache16896

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm138 : Finset ℤ := Finset.Ioc (639) (703)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm138

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm138)

def idx (n : ℤ) : ℕ := (n - (511)).toNat

lemma mem_wMm138 {n : ℤ} (hn : n ∈ wMm138) : (639) < n ∧ n ≤ (703) := by
  simpa only [wMm138, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm138) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm138 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm138) :
    2 * Cache16896.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm138 hn
  simp only [idx, Cache16896.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm138) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm138 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm138) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm138 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm138) :
    sampleNumerator (2 * n + 1) =
      (Cache16896.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache16896.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm138) :
    sampleRadius (2 * n + 1) =
      (Cache16896.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache16896.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm138_c_fast : tableEnergyNumerator t wMm138 4 1 = (39727250487244745186782309373917256213383711145404066402035917551244209407881900465587413109578589 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm138 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm138 4 1 =
      ∑ n ∈ wMm138, ((6 * n + 4) ^ 2 - 4) *
        ((Cache16896.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm138_r_fast : tableEnergyRadius t wMm138 4 1 = (139735371260430519820560402273412960149713473689706870958386339526500221878354943812007122 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm138 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm138 4 1 =
      ∑ n ∈ wMm138, (|((6 * n + 4) ^ 2 - 4)| * (Cache16896.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache16896.entries[idx n]?.getD (0, 0)).1| +
          (Cache16896.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm138

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm138_c : tableEnergyNumerator t wMm138 4 1 = (39727250487244745186782309373917256213383711145404066402035917551244209407881900465587413109578589 : ℤ) := by
  exact KsIndex.NegSignProdFastMm138.eMm138_c_fast
theorem eMm138_r : tableEnergyRadius t wMm138 4 1 = (139735371260430519820560402273412960149713473689706870958386339526500221878354943812007122 : ℤ) := by
  exact KsIndex.NegSignProdFastMm138.eMm138_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm138_c
#print axioms KsIndex.NegSignProd.eMm138_r
