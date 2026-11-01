module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache22016

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm217 : Finset ℤ := Finset.Ioc (5695) (5759)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm217

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm217)

def idx (n : ℤ) : ℕ := (n - (5631)).toNat

lemma mem_wMm217 {n : ℤ} (hn : n ∈ wMm217) : (5695) < n ∧ n ≤ (5759) := by
  simpa only [wMm217, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm217) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm217 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm217) :
    2 * Cache22016.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm217 hn
  simp only [idx, Cache22016.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm217) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm217 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm217) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm217 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm217) :
    sampleNumerator (2 * n + 1) =
      (Cache22016.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache22016.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm217) :
    sampleRadius (2 * n + 1) =
      (Cache22016.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache22016.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm217_c_fast : tableEnergyNumerator t wMm217 4 1 = (586608462363807773535857200583340062866931830955798857284181623220717167711453762012347923960399 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm217 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm217 4 1 =
      ∑ n ∈ wMm217, ((6 * n + 4) ^ 2 - 4) *
        ((Cache22016.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm217_r_fast : tableEnergyRadius t wMm217 4 1 = (1830030590708056068423944817466218871993038307006874426602943469007054576835232201599491 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm217 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm217 4 1 =
      ∑ n ∈ wMm217, (|((6 * n + 4) ^ 2 - 4)| * (Cache22016.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache22016.entries[idx n]?.getD (0, 0)).1| +
          (Cache22016.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm217

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm217_c : tableEnergyNumerator t wMm217 4 1 = (586608462363807773535857200583340062866931830955798857284181623220717167711453762012347923960399 : ℤ) := by
  exact KsIndex.NegSignProdFastMm217.eMm217_c_fast
theorem eMm217_r : tableEnergyRadius t wMm217 4 1 = (1830030590708056068423944817466218871993038307006874426602943469007054576835232201599491 : ℤ) := by
  exact KsIndex.NegSignProdFastMm217.eMm217_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm217_c
#print axioms KsIndex.NegSignProd.eMm217_r
