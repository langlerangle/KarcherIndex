module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache16640

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm132 : Finset ℤ := Finset.Ioc (255) (319)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm132

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm132)

def idx (n : ℤ) : ℕ := (n - (255)).toNat

lemma mem_wMm132 {n : ℤ} (hn : n ∈ wMm132) : (255) < n ∧ n ≤ (319) := by
  simpa only [wMm132, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm132) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm132 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm132) :
    2 * Cache16640.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm132 hn
  simp only [idx, Cache16640.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm132) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm132 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm132) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm132 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm132) :
    sampleNumerator (2 * n + 1) =
      (Cache16640.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache16640.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm132) :
    sampleRadius (2 * n + 1) =
      (Cache16640.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache16640.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm132_c_fast : tableEnergyNumerator t wMm132 4 1 = (214531331833439147828892287952882608553320486106508146319419724344316116153929379670803782800258387 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm132 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm132 4 1 =
      ∑ n ∈ wMm132, ((6 * n + 4) ^ 2 - 4) *
        ((Cache16640.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm132_r_fast : tableEnergyRadius t wMm132 4 1 = (790457937462349694570777787033307436640830220699140715603841425684216730015920058665733827 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm132 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm132 4 1 =
      ∑ n ∈ wMm132, (|((6 * n + 4) ^ 2 - 4)| * (Cache16640.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache16640.entries[idx n]?.getD (0, 0)).1| +
          (Cache16640.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm132

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm132_c : tableEnergyNumerator t wMm132 4 1 = (214531331833439147828892287952882608553320486106508146319419724344316116153929379670803782800258387 : ℤ) := by
  exact KsIndex.NegSignProdFastMm132.eMm132_c_fast
theorem eMm132_r : tableEnergyRadius t wMm132 4 1 = (790457937462349694570777787033307436640830220699140715603841425684216730015920058665733827 : ℤ) := by
  exact KsIndex.NegSignProdFastMm132.eMm132_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm132_c
#print axioms KsIndex.NegSignProd.eMm132_r
