module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache10240

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm34 : Finset ℤ := Finset.Ioc (-6017) (-5953)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm34

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm34)

def idx (n : ℤ) : ℕ := (n - (-6145)).toNat

lemma mem_wMm34 {n : ℤ} (hn : n ∈ wMm34) : (-6017) < n ∧ n ≤ (-5953) := by
  simpa only [wMm34, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm34) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm34 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm34) :
    2 * Cache10240.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm34 hn
  simp only [idx, Cache10240.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm34) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm34 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm34) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm34 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm34) :
    sampleNumerator (2 * n + 1) =
      (Cache10240.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache10240.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm34) :
    sampleRadius (2 * n + 1) =
      (Cache10240.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache10240.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm34_c_fast : tableEnergyNumerator t wMm34 4 1 = (54434928722749251013712292423668936876366163039008192417117418808249242521492811475493090250862 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm34 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm34 4 1 =
      ∑ n ∈ wMm34, ((6 * n + 4) ^ 2 - 4) *
        ((Cache10240.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm34_r_fast : tableEnergyRadius t wMm34 4 1 = (532778178158564868965192280366265734349022111983839258878320219793901686047028587651919 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm34 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm34 4 1 =
      ∑ n ∈ wMm34, (|((6 * n + 4) ^ 2 - 4)| * (Cache10240.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache10240.entries[idx n]?.getD (0, 0)).1| +
          (Cache10240.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm34

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm34_c : tableEnergyNumerator t wMm34 4 1 = (54434928722749251013712292423668936876366163039008192417117418808249242521492811475493090250862 : ℤ) := by
  exact KsIndex.NegSignProdFastMm34.eMm34_c_fast
theorem eMm34_r : tableEnergyRadius t wMm34 4 1 = (532778178158564868965192280366265734349022111983839258878320219793901686047028587651919 : ℤ) := by
  exact KsIndex.NegSignProdFastMm34.eMm34_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm34_c
#print axioms KsIndex.NegSignProd.eMm34_r
