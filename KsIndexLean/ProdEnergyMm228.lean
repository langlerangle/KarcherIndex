module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache22784

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm228 : Finset ℤ := Finset.Ioc (6399) (6463)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm228

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm228)

def idx (n : ℤ) : ℕ := (n - (6399)).toNat

lemma mem_wMm228 {n : ℤ} (hn : n ∈ wMm228) : (6399) < n ∧ n ≤ (6463) := by
  simpa only [wMm228, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm228) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm228 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm228) :
    2 * Cache22784.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm228 hn
  simp only [idx, Cache22784.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm228) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm228 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm228) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm228 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm228) :
    sampleNumerator (2 * n + 1) =
      (Cache22784.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache22784.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm228) :
    sampleRadius (2 * n + 1) =
      (Cache22784.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache22784.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm228_c_fast : tableEnergyNumerator t wMm228 4 1 = (467556430517601752473315841480990653151236464558749941956126609827327278167302723005294784249914 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm228 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm228 4 1 =
      ∑ n ∈ wMm228, ((6 * n + 4) ^ 2 - 4) *
        ((Cache22784.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm228_r_fast : tableEnergyRadius t wMm228 4 1 = (1449014242885400275025830993377637514929599332922103837112839347692365769695681939187466 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm228 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm228 4 1 =
      ∑ n ∈ wMm228, (|((6 * n + 4) ^ 2 - 4)| * (Cache22784.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache22784.entries[idx n]?.getD (0, 0)).1| +
          (Cache22784.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm228

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm228_c : tableEnergyNumerator t wMm228 4 1 = (467556430517601752473315841480990653151236464558749941956126609827327278167302723005294784249914 : ℤ) := by
  exact KsIndex.NegSignProdFastMm228.eMm228_c_fast
theorem eMm228_r : tableEnergyRadius t wMm228 4 1 = (1449014242885400275025830993377637514929599332922103837112839347692365769695681939187466 : ℤ) := by
  exact KsIndex.NegSignProdFastMm228.eMm228_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm228_c
#print axioms KsIndex.NegSignProd.eMm228_r
