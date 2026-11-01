module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache12544

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm68 : Finset ℤ := Finset.Ioc (-3841) (-3777)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm68

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm68)

def idx (n : ℤ) : ℕ := (n - (-3841)).toNat

lemma mem_wMm68 {n : ℤ} (hn : n ∈ wMm68) : (-3841) < n ∧ n ≤ (-3777) := by
  simpa only [wMm68, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm68) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm68 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm68) :
    2 * Cache12544.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm68 hn
  simp only [idx, Cache12544.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm68) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm68 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm68) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm68 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm68) :
    sampleNumerator (2 * n + 1) =
      (Cache12544.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache12544.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm68) :
    sampleRadius (2 * n + 1) =
      (Cache12544.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache12544.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm68_c_fast : tableEnergyNumerator t wMm68 4 1 = (109922615968790820974153982255488429456433495269505239324247422888915720142808941060162228559122 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm68 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm68 4 1 =
      ∑ n ∈ wMm68, ((6 * n + 4) ^ 2 - 4) *
        ((Cache12544.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm68_r_fast : tableEnergyRadius t wMm68 4 1 = (1209372725699289919748195215782259506092833505087389299701077147673506636808625225946853 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm68 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm68 4 1 =
      ∑ n ∈ wMm68, (|((6 * n + 4) ^ 2 - 4)| * (Cache12544.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache12544.entries[idx n]?.getD (0, 0)).1| +
          (Cache12544.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm68

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm68_c : tableEnergyNumerator t wMm68 4 1 = (109922615968790820974153982255488429456433495269505239324247422888915720142808941060162228559122 : ℤ) := by
  exact KsIndex.NegSignProdFastMm68.eMm68_c_fast
theorem eMm68_r : tableEnergyRadius t wMm68 4 1 = (1209372725699289919748195215782259506092833505087389299701077147673506636808625225946853 : ℤ) := by
  exact KsIndex.NegSignProdFastMm68.eMm68_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm68_c
#print axioms KsIndex.NegSignProd.eMm68_r
