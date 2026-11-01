module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache15360

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm113 : Finset ℤ := Finset.Ioc (-961) (-897)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm113

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm113)

def idx (n : ℤ) : ℕ := (n - (-1025)).toNat

lemma mem_wMm113 {n : ℤ} (hn : n ∈ wMm113) : (-961) < n ∧ n ≤ (-897) := by
  simpa only [wMm113, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm113) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm113 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm113) :
    2 * Cache15360.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm113 hn
  simp only [idx, Cache15360.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm113) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm113 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm113) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm113 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm113) :
    sampleNumerator (2 * n + 1) =
      (Cache15360.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache15360.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm113) :
    sampleRadius (2 * n + 1) =
      (Cache15360.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache15360.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm113_c_fast : tableEnergyNumerator t wMm113 4 1 = (843631467030669659087256105242086049932429622494516828579098090177143691561063410466739061846189 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm113 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm113 4 1 =
      ∑ n ∈ wMm113, ((6 * n + 4) ^ 2 - 4) *
        ((Cache15360.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm113_r_fast : tableEnergyRadius t wMm113 4 1 = (14536381212230617477176680860146164090351689424710423106582180134543905641972572438982727 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm113 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm113 4 1 =
      ∑ n ∈ wMm113, (|((6 * n + 4) ^ 2 - 4)| * (Cache15360.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache15360.entries[idx n]?.getD (0, 0)).1| +
          (Cache15360.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm113

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm113_c : tableEnergyNumerator t wMm113 4 1 = (843631467030669659087256105242086049932429622494516828579098090177143691561063410466739061846189 : ℤ) := by
  exact KsIndex.NegSignProdFastMm113.eMm113_c_fast
theorem eMm113_r : tableEnergyRadius t wMm113 4 1 = (14536381212230617477176680860146164090351689424710423106582180134543905641972572438982727 : ℤ) := by
  exact KsIndex.NegSignProdFastMm113.eMm113_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm113_c
#print axioms KsIndex.NegSignProd.eMm113_r
