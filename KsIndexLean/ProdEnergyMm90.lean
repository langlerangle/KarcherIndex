module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache13824

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm90 : Finset ℤ := Finset.Ioc (-2433) (-2369)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm90

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm90)

def idx (n : ℤ) : ℕ := (n - (-2561)).toNat

lemma mem_wMm90 {n : ℤ} (hn : n ∈ wMm90) : (-2433) < n ∧ n ≤ (-2369) := by
  simpa only [wMm90, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm90) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm90 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm90) :
    2 * Cache13824.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm90 hn
  simp only [idx, Cache13824.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm90) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm90 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm90) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm90 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm90) :
    sampleNumerator (2 * n + 1) =
      (Cache13824.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache13824.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm90) :
    sampleRadius (2 * n + 1) =
      (Cache13824.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache13824.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm90_c_fast : tableEnergyNumerator t wMm90 4 1 = (220620541352076154758502693228796983028713471315478972009877739548358317077383222626454861448143 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm90 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm90 4 1 =
      ∑ n ∈ wMm90, ((6 * n + 4) ^ 2 - 4) *
        ((Cache13824.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm90_r_fast : tableEnergyRadius t wMm90 4 1 = (2766291451605214429456003080775230180426047500351818890733193485325090089214172896324144 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm90 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm90 4 1 =
      ∑ n ∈ wMm90, (|((6 * n + 4) ^ 2 - 4)| * (Cache13824.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache13824.entries[idx n]?.getD (0, 0)).1| +
          (Cache13824.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm90

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm90_c : tableEnergyNumerator t wMm90 4 1 = (220620541352076154758502693228796983028713471315478972009877739548358317077383222626454861448143 : ℤ) := by
  exact KsIndex.NegSignProdFastMm90.eMm90_c_fast
theorem eMm90_r : tableEnergyRadius t wMm90 4 1 = (2766291451605214429456003080775230180426047500351818890733193485325090089214172896324144 : ℤ) := by
  exact KsIndex.NegSignProdFastMm90.eMm90_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm90_c
#print axioms KsIndex.NegSignProd.eMm90_r
