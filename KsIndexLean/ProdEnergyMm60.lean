module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache12032

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm60 : Finset ℤ := Finset.Ioc (-4353) (-4289)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm60

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm60)

def idx (n : ℤ) : ℕ := (n - (-4353)).toNat

lemma mem_wMm60 {n : ℤ} (hn : n ∈ wMm60) : (-4353) < n ∧ n ≤ (-4289) := by
  simpa only [wMm60, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm60) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm60 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm60) :
    2 * Cache12032.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm60 hn
  simp only [idx, Cache12032.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm60) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm60 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm60) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm60 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm60) :
    sampleNumerator (2 * n + 1) =
      (Cache12032.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache12032.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm60) :
    sampleRadius (2 * n + 1) =
      (Cache12032.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache12032.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm60_c_fast : tableEnergyNumerator t wMm60 4 1 = (90513926358456306489217191072162269519530191719349755941725953269769715537722003322924710968264 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm60 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm60 4 1 =
      ∑ n ∈ wMm60, ((6 * n + 4) ^ 2 - 4) *
        ((Cache12032.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm60_r_fast : tableEnergyRadius t wMm60 4 1 = (962879786653456250346325324692315293295054921992261502594496013811291975723681762907498 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm60 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm60 4 1 =
      ∑ n ∈ wMm60, (|((6 * n + 4) ^ 2 - 4)| * (Cache12032.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache12032.entries[idx n]?.getD (0, 0)).1| +
          (Cache12032.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm60

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm60_c : tableEnergyNumerator t wMm60 4 1 = (90513926358456306489217191072162269519530191719349755941725953269769715537722003322924710968264 : ℤ) := by
  exact KsIndex.NegSignProdFastMm60.eMm60_c_fast
theorem eMm60_r : tableEnergyRadius t wMm60 4 1 = (962879786653456250346325324692315293295054921992261502594496013811291975723681762907498 : ℤ) := by
  exact KsIndex.NegSignProdFastMm60.eMm60_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm60_c
#print axioms KsIndex.NegSignProd.eMm60_r
