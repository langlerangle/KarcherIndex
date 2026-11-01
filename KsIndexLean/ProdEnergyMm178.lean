module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache19456

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm178 : Finset ℤ := Finset.Ioc (3199) (3263)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm178

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm178)

def idx (n : ℤ) : ℕ := (n - (3071)).toNat

lemma mem_wMm178 {n : ℤ} (hn : n ∈ wMm178) : (3199) < n ∧ n ≤ (3263) := by
  simpa only [wMm178, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm178) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm178 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm178) :
    2 * Cache19456.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm178 hn
  simp only [idx, Cache19456.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm178) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm178 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm178) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm178 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm178) :
    sampleNumerator (2 * n + 1) =
      (Cache19456.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache19456.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm178) :
    sampleRadius (2 * n + 1) =
      (Cache19456.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache19456.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm178_c_fast : tableEnergyNumerator t wMm178 4 1 = (1800557114530320802640792438743506605369997357552661512447507652646004238788237428101217538958407 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm178 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm178 4 1 =
      ∑ n ∈ wMm178, ((6 * n + 4) ^ 2 - 4) *
        ((Cache19456.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm178_r_fast : tableEnergyRadius t wMm178 4 1 = (5802608757731565636103993509856141408506769716628270567775358994767484846817029334413725 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm178 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm178 4 1 =
      ∑ n ∈ wMm178, (|((6 * n + 4) ^ 2 - 4)| * (Cache19456.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache19456.entries[idx n]?.getD (0, 0)).1| +
          (Cache19456.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm178

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm178_c : tableEnergyNumerator t wMm178 4 1 = (1800557114530320802640792438743506605369997357552661512447507652646004238788237428101217538958407 : ℤ) := by
  exact KsIndex.NegSignProdFastMm178.eMm178_c_fast
theorem eMm178_r : tableEnergyRadius t wMm178 4 1 = (5802608757731565636103993509856141408506769716628270567775358994767484846817029334413725 : ℤ) := by
  exact KsIndex.NegSignProdFastMm178.eMm178_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm178_c
#print axioms KsIndex.NegSignProd.eMm178_r
