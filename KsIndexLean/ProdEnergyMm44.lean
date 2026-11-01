module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache11008

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm44 : Finset ℤ := Finset.Ioc (-5377) (-5313)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm44

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm44)

def idx (n : ℤ) : ℕ := (n - (-5377)).toNat

lemma mem_wMm44 {n : ℤ} (hn : n ∈ wMm44) : (-5377) < n ∧ n ≤ (-5313) := by
  simpa only [wMm44, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm44) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm44 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm44) :
    2 * Cache11008.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm44 hn
  simp only [idx, Cache11008.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm44) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm44 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm44) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm44 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm44) :
    sampleNumerator (2 * n + 1) =
      (Cache11008.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache11008.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm44) :
    sampleRadius (2 * n + 1) =
      (Cache11008.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache11008.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm44_c_fast : tableEnergyNumerator t wMm44 4 1 = (65012292780203176298605629167624098370712259392249756177793323618456127168223867200857845280104 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm44 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm44 4 1 =
      ∑ n ∈ wMm44, ((6 * n + 4) ^ 2 - 4) *
        ((Cache11008.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm44_r_fast : tableEnergyRadius t wMm44 4 1 = (654610713104519022079395378072127848064436117734321085572495202659156771644943914432301 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm44 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm44 4 1 =
      ∑ n ∈ wMm44, (|((6 * n + 4) ^ 2 - 4)| * (Cache11008.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache11008.entries[idx n]?.getD (0, 0)).1| +
          (Cache11008.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm44

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm44_c : tableEnergyNumerator t wMm44 4 1 = (65012292780203176298605629167624098370712259392249756177793323618456127168223867200857845280104 : ℤ) := by
  exact KsIndex.NegSignProdFastMm44.eMm44_c_fast
theorem eMm44_r : tableEnergyRadius t wMm44 4 1 = (654610713104519022079395378072127848064436117734321085572495202659156771644943914432301 : ℤ) := by
  exact KsIndex.NegSignProdFastMm44.eMm44_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm44_c
#print axioms KsIndex.NegSignProd.eMm44_r
