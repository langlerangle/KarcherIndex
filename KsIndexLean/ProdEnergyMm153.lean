module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache17920

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm153 : Finset ℤ := Finset.Ioc (1599) (1663)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm153

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm153)

def idx (n : ℤ) : ℕ := (n - (1535)).toNat

lemma mem_wMm153 {n : ℤ} (hn : n ∈ wMm153) : (1599) < n ∧ n ≤ (1663) := by
  simpa only [wMm153, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm153) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm153 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm153) :
    2 * Cache17920.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm153 hn
  simp only [idx, Cache17920.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm153) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm153 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm153) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm153 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm153) :
    sampleNumerator (2 * n + 1) =
      (Cache17920.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache17920.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm153) :
    sampleRadius (2 * n + 1) =
      (Cache17920.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache17920.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm153_c_fast : tableEnergyNumerator t wMm153 4 1 = (6896020236986052574277281013981758135777327560489944508328918086133649806250884041281265500530111 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm153 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm153 4 1 =
      ∑ n ∈ wMm153, ((6 * n + 4) ^ 2 - 4) *
        ((Cache17920.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm153_r_fast : tableEnergyRadius t wMm153 4 1 = (23093145332231558082687360937734304232208176038598356624269349141172622096494255321065115 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm153 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm153 4 1 =
      ∑ n ∈ wMm153, (|((6 * n + 4) ^ 2 - 4)| * (Cache17920.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache17920.entries[idx n]?.getD (0, 0)).1| +
          (Cache17920.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm153

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm153_c : tableEnergyNumerator t wMm153 4 1 = (6896020236986052574277281013981758135777327560489944508328918086133649806250884041281265500530111 : ℤ) := by
  exact KsIndex.NegSignProdFastMm153.eMm153_c_fast
theorem eMm153_r : tableEnergyRadius t wMm153 4 1 = (23093145332231558082687360937734304232208176038598356624269349141172622096494255321065115 : ℤ) := by
  exact KsIndex.NegSignProdFastMm153.eMm153_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm153_c
#print axioms KsIndex.NegSignProd.eMm153_r
