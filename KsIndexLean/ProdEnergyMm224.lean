module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache22528

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm224 : Finset ℤ := Finset.Ioc (6143) (6207)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm224

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm224)

def idx (n : ℤ) : ℕ := (n - (6143)).toNat

lemma mem_wMm224 {n : ℤ} (hn : n ∈ wMm224) : (6143) < n ∧ n ≤ (6207) := by
  simpa only [wMm224, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm224) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm224 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm224) :
    2 * Cache22528.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm224 hn
  simp only [idx, Cache22528.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm224) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm224 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm224) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm224 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm224) :
    sampleNumerator (2 * n + 1) =
      (Cache22528.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache22528.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm224) :
    sampleRadius (2 * n + 1) =
      (Cache22528.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache22528.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm224_c_fast : tableEnergyNumerator t wMm224 4 1 = (506226788401711544310332487009719881211311748246891365428560436705632416514941508603528690036157 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm224 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm224 4 1 =
      ∑ n ∈ wMm224, ((6 * n + 4) ^ 2 - 4) *
        ((Cache22528.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm224_r_fast : tableEnergyRadius t wMm224 4 1 = (1572498679358309325666839620080372954529209587355769622407341190050080648485358620434548 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm224 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm224 4 1 =
      ∑ n ∈ wMm224, (|((6 * n + 4) ^ 2 - 4)| * (Cache22528.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache22528.entries[idx n]?.getD (0, 0)).1| +
          (Cache22528.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm224

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm224_c : tableEnergyNumerator t wMm224 4 1 = (506226788401711544310332487009719881211311748246891365428560436705632416514941508603528690036157 : ℤ) := by
  exact KsIndex.NegSignProdFastMm224.eMm224_c_fast
theorem eMm224_r : tableEnergyRadius t wMm224 4 1 = (1572498679358309325666839620080372954529209587355769622407341190050080648485358620434548 : ℤ) := by
  exact KsIndex.NegSignProdFastMm224.eMm224_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm224_c
#print axioms KsIndex.NegSignProd.eMm224_r
