module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache13824

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm88 : Finset ℤ := Finset.Ioc (-2561) (-2497)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm88

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm88)

def idx (n : ℤ) : ℕ := (n - (-2561)).toNat

lemma mem_wMm88 {n : ℤ} (hn : n ∈ wMm88) : (-2561) < n ∧ n ≤ (-2497) := by
  simpa only [wMm88, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm88) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm88 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm88) :
    2 * Cache13824.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm88 hn
  simp only [idx, Cache13824.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm88) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm88 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm88) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm88 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm88) :
    sampleNumerator (2 * n + 1) =
      (Cache13824.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache13824.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm88) :
    sampleRadius (2 * n + 1) =
      (Cache13824.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache13824.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm88_c_fast : tableEnergyNumerator t wMm88 4 1 = (204230290448506997016573626224589544869984590181968294355014209402908205492700808594178803958985 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm88 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm88 4 1 =
      ∑ n ∈ wMm88, ((6 * n + 4) ^ 2 - 4) *
        ((Cache13824.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm88_r_fast : tableEnergyRadius t wMm88 4 1 = (2521745502783510182480902181000621294517882592700193636622121480383608739080210201030555 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm88 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm88 4 1 =
      ∑ n ∈ wMm88, (|((6 * n + 4) ^ 2 - 4)| * (Cache13824.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache13824.entries[idx n]?.getD (0, 0)).1| +
          (Cache13824.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm88

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm88_c : tableEnergyNumerator t wMm88 4 1 = (204230290448506997016573626224589544869984590181968294355014209402908205492700808594178803958985 : ℤ) := by
  exact KsIndex.NegSignProdFastMm88.eMm88_c_fast
theorem eMm88_r : tableEnergyRadius t wMm88 4 1 = (2521745502783510182480902181000621294517882592700193636622121480383608739080210201030555 : ℤ) := by
  exact KsIndex.NegSignProdFastMm88.eMm88_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm88_c
#print axioms KsIndex.NegSignProd.eMm88_r
