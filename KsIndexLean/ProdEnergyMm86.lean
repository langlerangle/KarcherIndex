module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache13568

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm86 : Finset ℤ := Finset.Ioc (-2689) (-2625)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm86

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm86)

def idx (n : ℤ) : ℕ := (n - (-2817)).toNat

lemma mem_wMm86 {n : ℤ} (hn : n ∈ wMm86) : (-2689) < n ∧ n ≤ (-2625) := by
  simpa only [wMm86, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm86) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm86 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm86) :
    2 * Cache13568.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm86 hn
  simp only [idx, Cache13568.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm86) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm86 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm86) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm86 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm86) :
    sampleNumerator (2 * n + 1) =
      (Cache13568.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache13568.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm86) :
    sampleRadius (2 * n + 1) =
      (Cache13568.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache13568.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm86_c_fast : tableEnergyNumerator t wMm86 4 1 = (189722471780004650551072066970104951439347810033246729017194250694793826894699727757712774233402 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm86 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm86 4 1 =
      ∑ n ∈ wMm86, ((6 * n + 4) ^ 2 - 4) *
        ((Cache13568.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm86_r_fast : tableEnergyRadius t wMm86 4 1 = (2309022660295704960943696125334476508353841026672202019564640060516115412499246896812255 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm86 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm86 4 1 =
      ∑ n ∈ wMm86, (|((6 * n + 4) ^ 2 - 4)| * (Cache13568.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache13568.entries[idx n]?.getD (0, 0)).1| +
          (Cache13568.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm86

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm86_c : tableEnergyNumerator t wMm86 4 1 = (189722471780004650551072066970104951439347810033246729017194250694793826894699727757712774233402 : ℤ) := by
  exact KsIndex.NegSignProdFastMm86.eMm86_c_fast
theorem eMm86_r : tableEnergyRadius t wMm86 4 1 = (2309022660295704960943696125334476508353841026672202019564640060516115412499246896812255 : ℤ) := by
  exact KsIndex.NegSignProdFastMm86.eMm86_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm86_c
#print axioms KsIndex.NegSignProd.eMm86_r
