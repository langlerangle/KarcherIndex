module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache22784

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm230 : Finset ℤ := Finset.Ioc (6527) (6591)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm230

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm230)

def idx (n : ℤ) : ℕ := (n - (6399)).toNat

lemma mem_wMm230 {n : ℤ} (hn : n ∈ wMm230) : (6527) < n ∧ n ≤ (6591) := by
  simpa only [wMm230, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm230) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm230 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm230) :
    2 * Cache22784.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm230 hn
  simp only [idx, Cache22784.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm230) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm230 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm230) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm230 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm230) :
    sampleNumerator (2 * n + 1) =
      (Cache22784.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache22784.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm230) :
    sampleRadius (2 * n + 1) =
      (Cache22784.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache22784.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm230_c_fast : tableEnergyNumerator t wMm230 4 1 = (449875550842707671903332216659511961471018308046599060713164510029693956073453508770225596846556 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm230 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm230 4 1 =
      ∑ n ∈ wMm230, ((6 * n + 4) ^ 2 - 4) *
        ((Cache22784.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm230_r_fast : tableEnergyRadius t wMm230 4 1 = (1392651589222158375083862829267284561285809128886318357172030592122867695435892412614214 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm230 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm230 4 1 =
      ∑ n ∈ wMm230, (|((6 * n + 4) ^ 2 - 4)| * (Cache22784.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache22784.entries[idx n]?.getD (0, 0)).1| +
          (Cache22784.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm230

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm230_c : tableEnergyNumerator t wMm230 4 1 = (449875550842707671903332216659511961471018308046599060713164510029693956073453508770225596846556 : ℤ) := by
  exact KsIndex.NegSignProdFastMm230.eMm230_c_fast
theorem eMm230_r : tableEnergyRadius t wMm230 4 1 = (1392651589222158375083862829267284561285809128886318357172030592122867695435892412614214 : ℤ) := by
  exact KsIndex.NegSignProdFastMm230.eMm230_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm230_c
#print axioms KsIndex.NegSignProd.eMm230_r
