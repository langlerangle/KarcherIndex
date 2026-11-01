module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache11264

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm49 : Finset ℤ := Finset.Ioc (-5057) (-4993)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm49

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm49)

def idx (n : ℤ) : ℕ := (n - (-5121)).toNat

lemma mem_wMm49 {n : ℤ} (hn : n ∈ wMm49) : (-5057) < n ∧ n ≤ (-4993) := by
  simpa only [wMm49, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm49) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm49 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm49) :
    2 * Cache11264.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm49 hn
  simp only [idx, Cache11264.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm49) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm49 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm49) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm49 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm49) :
    sampleNumerator (2 * n + 1) =
      (Cache11264.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache11264.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm49) :
    sampleRadius (2 * n + 1) =
      (Cache11264.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache11264.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm49_c_fast : tableEnergyNumerator t wMm49 4 1 = (71596931638845985397872891862670707559015018252002253501760900296523173411717950554990337024613 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm49 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm49 4 1 =
      ∑ n ∈ wMm49, ((6 * n + 4) ^ 2 - 4) *
        ((Cache11264.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm49_r_fast : tableEnergyRadius t wMm49 4 1 = (732342080647997917652687937891229407049942329932416385670883316001608760954878025110555 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm49 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm49 4 1 =
      ∑ n ∈ wMm49, (|((6 * n + 4) ^ 2 - 4)| * (Cache11264.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache11264.entries[idx n]?.getD (0, 0)).1| +
          (Cache11264.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm49

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm49_c : tableEnergyNumerator t wMm49 4 1 = (71596931638845985397872891862670707559015018252002253501760900296523173411717950554990337024613 : ℤ) := by
  exact KsIndex.NegSignProdFastMm49.eMm49_c_fast
theorem eMm49_r : tableEnergyRadius t wMm49 4 1 = (732342080647997917652687937891229407049942329932416385670883316001608760954878025110555 : ℤ) := by
  exact KsIndex.NegSignProdFastMm49.eMm49_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm49_c
#print axioms KsIndex.NegSignProd.eMm49_r
