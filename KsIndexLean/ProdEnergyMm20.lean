module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache9472

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm20 : Finset ℤ := Finset.Ioc (-6913) (-6849)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm20

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm20)

def idx (n : ℤ) : ℕ := (n - (-6913)).toNat

lemma mem_wMm20 {n : ℤ} (hn : n ∈ wMm20) : (-6913) < n ∧ n ≤ (-6849) := by
  simpa only [wMm20, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm20) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm20 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm20) :
    2 * Cache9472.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm20 hn
  simp only [idx, Cache9472.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm20) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm20 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm20) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm20 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm20) :
    sampleNumerator (2 * n + 1) =
      (Cache9472.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache9472.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm20) :
    sampleRadius (2 * n + 1) =
      (Cache9472.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache9472.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm20_c_fast : tableEnergyNumerator t wMm20 4 1 = (43664721103639346471022459294155944040163527102055238073076583027549913818472009422528295700569 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm20 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm20 4 1 =
      ∑ n ∈ wMm20, ((6 * n + 4) ^ 2 - 4) *
        ((Cache9472.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm20_r_fast : tableEnergyRadius t wMm20 4 1 = (412990377019222272038114594434270114287108082561599151125264128777607443245654373771375 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm20 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm20 4 1 =
      ∑ n ∈ wMm20, (|((6 * n + 4) ^ 2 - 4)| * (Cache9472.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache9472.entries[idx n]?.getD (0, 0)).1| +
          (Cache9472.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm20

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm20_c : tableEnergyNumerator t wMm20 4 1 = (43664721103639346471022459294155944040163527102055238073076583027549913818472009422528295700569 : ℤ) := by
  exact KsIndex.NegSignProdFastMm20.eMm20_c_fast
theorem eMm20_r : tableEnergyRadius t wMm20 4 1 = (412990377019222272038114594434270114287108082561599151125264128777607443245654373771375 : ℤ) := by
  exact KsIndex.NegSignProdFastMm20.eMm20_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm20_c
#print axioms KsIndex.NegSignProd.eMm20_r
