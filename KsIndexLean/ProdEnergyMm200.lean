module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache20992

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm200 : Finset ℤ := Finset.Ioc (4607) (4671)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm200

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm200)

def idx (n : ℤ) : ℕ := (n - (4607)).toNat

lemma mem_wMm200 {n : ℤ} (hn : n ∈ wMm200) : (4607) < n ∧ n ≤ (4671) := by
  simpa only [wMm200, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm200) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm200 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm200) :
    2 * Cache20992.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm200 hn
  simp only [idx, Cache20992.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm200) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm200 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm200) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm200 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm200) :
    sampleNumerator (2 * n + 1) =
      (Cache20992.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache20992.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm200) :
    sampleRadius (2 * n + 1) =
      (Cache20992.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache20992.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm200_c_fast : tableEnergyNumerator t wMm200 4 1 = (886126835171345627189981859877323414766001773783527717776968914143820337395248641324081315974129 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm200 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm200 4 1 =
      ∑ n ∈ wMm200, ((6 * n + 4) ^ 2 - 4) *
        ((Cache20992.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm200_r_fast : tableEnergyRadius t wMm200 4 1 = (2797772864336177763959054734848487954226172080960003787821879000054119987874938073831941 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm200 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm200 4 1 =
      ∑ n ∈ wMm200, (|((6 * n + 4) ^ 2 - 4)| * (Cache20992.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache20992.entries[idx n]?.getD (0, 0)).1| +
          (Cache20992.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm200

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm200_c : tableEnergyNumerator t wMm200 4 1 = (886126835171345627189981859877323414766001773783527717776968914143820337395248641324081315974129 : ℤ) := by
  exact KsIndex.NegSignProdFastMm200.eMm200_c_fast
theorem eMm200_r : tableEnergyRadius t wMm200 4 1 = (2797772864336177763959054734848487954226172080960003787821879000054119987874938073831941 : ℤ) := by
  exact KsIndex.NegSignProdFastMm200.eMm200_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm200_c
#print axioms KsIndex.NegSignProd.eMm200_r
