module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache14848

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm106 : Finset ℤ := Finset.Ioc (-1409) (-1345)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm106

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm106)

def idx (n : ℤ) : ℕ := (n - (-1537)).toNat

lemma mem_wMm106 {n : ℤ} (hn : n ∈ wMm106) : (-1409) < n ∧ n ≤ (-1345) := by
  simpa only [wMm106, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm106) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm106 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm106) :
    2 * Cache14848.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm106 hn
  simp only [idx, Cache14848.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm106) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm106 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm106) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm106 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm106) :
    sampleNumerator (2 * n + 1) =
      (Cache14848.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache14848.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm106) :
    sampleRadius (2 * n + 1) =
      (Cache14848.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache14848.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm106_c_fast : tableEnergyNumerator t wMm106 4 1 = (492657972432763448777222375402787189502571481009986689648885820253952457390551044158378730277864 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm106 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm106 4 1 =
      ∑ n ∈ wMm106, ((6 * n + 4) ^ 2 - 4) *
        ((Cache14848.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm106_r_fast : tableEnergyRadius t wMm106 4 1 = (7370447068255681558543859916855901388189738928654932653885031753141325302403358955007020 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm106 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm106 4 1 =
      ∑ n ∈ wMm106, (|((6 * n + 4) ^ 2 - 4)| * (Cache14848.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache14848.entries[idx n]?.getD (0, 0)).1| +
          (Cache14848.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm106

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm106_c : tableEnergyNumerator t wMm106 4 1 = (492657972432763448777222375402787189502571481009986689648885820253952457390551044158378730277864 : ℤ) := by
  exact KsIndex.NegSignProdFastMm106.eMm106_c_fast
theorem eMm106_r : tableEnergyRadius t wMm106 4 1 = (7370447068255681558543859916855901388189738928654932653885031753141325302403358955007020 : ℤ) := by
  exact KsIndex.NegSignProdFastMm106.eMm106_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm106_c
#print axioms KsIndex.NegSignProd.eMm106_r
