module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache8704

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm10 : Finset ℤ := Finset.Ioc (-7553) (-7489)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm10

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm10)

def idx (n : ℤ) : ℕ := (n - (-7681)).toNat

lemma mem_wMm10 {n : ℤ} (hn : n ∈ wMm10) : (-7553) < n ∧ n ≤ (-7489) := by
  simpa only [wMm10, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm10) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm10 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm10) :
    2 * Cache8704.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm10 hn
  simp only [idx, Cache8704.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm10) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm10 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm10) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm10 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm10) :
    sampleNumerator (2 * n + 1) =
      (Cache8704.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache8704.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm10) :
    sampleRadius (2 * n + 1) =
      (Cache8704.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache8704.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm10_c_fast : tableEnergyNumerator t wMm10 4 1 = (37909902450599828094906386687006484993934371453073464837143107549813097642733154052759960176987 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm10 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm10 4 1 =
      ∑ n ∈ wMm10, ((6 * n + 4) ^ 2 - 4) *
        ((Cache8704.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm10_r_fast : tableEnergyRadius t wMm10 4 1 = (350973778985499039055229625301991594560046872799620097120867576464093636338901962831945 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm10 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm10 4 1 =
      ∑ n ∈ wMm10, (|((6 * n + 4) ^ 2 - 4)| * (Cache8704.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache8704.entries[idx n]?.getD (0, 0)).1| +
          (Cache8704.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm10

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm10_c : tableEnergyNumerator t wMm10 4 1 = (37909902450599828094906386687006484993934371453073464837143107549813097642733154052759960176987 : ℤ) := by
  exact KsIndex.NegSignProdFastMm10.eMm10_c_fast
theorem eMm10_r : tableEnergyRadius t wMm10 4 1 = (350973778985499039055229625301991594560046872799620097120867576464093636338901962831945 : ℤ) := by
  exact KsIndex.NegSignProdFastMm10.eMm10_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm10_c
#print axioms KsIndex.NegSignProd.eMm10_r
