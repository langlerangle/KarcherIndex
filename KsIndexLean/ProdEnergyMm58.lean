module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache11776

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm58 : Finset ℤ := Finset.Ioc (-4481) (-4417)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm58

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm58)

def idx (n : ℤ) : ℕ := (n - (-4609)).toNat

lemma mem_wMm58 {n : ℤ} (hn : n ∈ wMm58) : (-4481) < n ∧ n ≤ (-4417) := by
  simpa only [wMm58, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm58) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm58 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm58) :
    2 * Cache11776.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm58 hn
  simp only [idx, Cache11776.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm58) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm58 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm58) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm58 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm58) :
    sampleNumerator (2 * n + 1) =
      (Cache11776.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache11776.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm58) :
    sampleRadius (2 * n + 1) =
      (Cache11776.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache11776.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm58_c_fast : tableEnergyNumerator t wMm58 4 1 = (86515282185022804892026180050671519341887704326161452577040638248900818029499708665291470212811 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm58 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm58 4 1 =
      ∑ n ∈ wMm58, ((6 * n + 4) ^ 2 - 4) *
        ((Cache11776.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm58_r_fast : tableEnergyRadius t wMm58 4 1 = (913306464001314876224004541442780203157980631645558770907196759563770185486371456628728 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm58 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm58 4 1 =
      ∑ n ∈ wMm58, (|((6 * n + 4) ^ 2 - 4)| * (Cache11776.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache11776.entries[idx n]?.getD (0, 0)).1| +
          (Cache11776.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm58

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm58_c : tableEnergyNumerator t wMm58 4 1 = (86515282185022804892026180050671519341887704326161452577040638248900818029499708665291470212811 : ℤ) := by
  exact KsIndex.NegSignProdFastMm58.eMm58_c_fast
theorem eMm58_r : tableEnergyRadius t wMm58 4 1 = (913306464001314876224004541442780203157980631645558770907196759563770185486371456628728 : ℤ) := by
  exact KsIndex.NegSignProdFastMm58.eMm58_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm58_c
#print axioms KsIndex.NegSignProd.eMm58_r
