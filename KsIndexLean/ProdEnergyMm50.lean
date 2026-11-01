module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache11264

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm50 : Finset ℤ := Finset.Ioc (-4993) (-4929)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm50

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm50)

def idx (n : ℤ) : ℕ := (n - (-5121)).toNat

lemma mem_wMm50 {n : ℤ} (hn : n ∈ wMm50) : (-4993) < n ∧ n ≤ (-4929) := by
  simpa only [wMm50, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm50) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm50 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm50) :
    2 * Cache11264.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm50 hn
  simp only [idx, Cache11264.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm50) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm50 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm50) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm50 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm50) :
    sampleNumerator (2 * n + 1) =
      (Cache11264.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache11264.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm50) :
    sampleRadius (2 * n + 1) =
      (Cache11264.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache11264.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm50_c_fast : tableEnergyNumerator t wMm50 4 1 = (73042523590123531202523643143016027204387367163142083541268177427907375100679790406817712357672 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm50 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm50 4 1 =
      ∑ n ∈ wMm50, ((6 * n + 4) ^ 2 - 4) *
        ((Cache11264.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm50_r_fast : tableEnergyRadius t wMm50 4 1 = (749589675960790494702551252871518325714562704581274102092054899523705709001373117536757 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm50 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm50 4 1 =
      ∑ n ∈ wMm50, (|((6 * n + 4) ^ 2 - 4)| * (Cache11264.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache11264.entries[idx n]?.getD (0, 0)).1| +
          (Cache11264.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm50

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm50_c : tableEnergyNumerator t wMm50 4 1 = (73042523590123531202523643143016027204387367163142083541268177427907375100679790406817712357672 : ℤ) := by
  exact KsIndex.NegSignProdFastMm50.eMm50_c_fast
theorem eMm50_r : tableEnergyRadius t wMm50 4 1 = (749589675960790494702551252871518325714562704581274102092054899523705709001373117536757 : ℤ) := by
  exact KsIndex.NegSignProdFastMm50.eMm50_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm50_c
#print axioms KsIndex.NegSignProd.eMm50_r
