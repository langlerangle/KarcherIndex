module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache14080

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm92 : Finset ℤ := Finset.Ioc (-2305) (-2241)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm92

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm92)

def idx (n : ℤ) : ℕ := (n - (-2305)).toNat

lemma mem_wMm92 {n : ℤ} (hn : n ∈ wMm92) : (-2305) < n ∧ n ≤ (-2241) := by
  simpa only [wMm92, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm92) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm92 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm92) :
    2 * Cache14080.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm92 hn
  simp only [idx, Cache14080.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm92) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm92 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm92) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm92 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm92) :
    sampleNumerator (2 * n + 1) =
      (Cache14080.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache14080.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm92) :
    sampleRadius (2 * n + 1) =
      (Cache14080.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache14080.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm92_c_fast : tableEnergyNumerator t wMm92 4 1 = (239249673723076806018181859107359240867590436788556510238881684573448696402464520790295998058603 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm92 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm92 4 1 =
      ∑ n ∈ wMm92, ((6 * n + 4) ^ 2 - 4) *
        ((Cache14080.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm92_r_fast : tableEnergyRadius t wMm92 4 1 = (3049463604760551230125250654003856810672823572337114918530381758599745625814690622411665 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm92 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm92 4 1 =
      ∑ n ∈ wMm92, (|((6 * n + 4) ^ 2 - 4)| * (Cache14080.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache14080.entries[idx n]?.getD (0, 0)).1| +
          (Cache14080.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm92

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm92_c : tableEnergyNumerator t wMm92 4 1 = (239249673723076806018181859107359240867590436788556510238881684573448696402464520790295998058603 : ℤ) := by
  exact KsIndex.NegSignProdFastMm92.eMm92_c_fast
theorem eMm92_r : tableEnergyRadius t wMm92 4 1 = (3049463604760551230125250654003856810672823572337114918530381758599745625814690622411665 : ℤ) := by
  exact KsIndex.NegSignProdFastMm92.eMm92_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm92_c
#print axioms KsIndex.NegSignProd.eMm92_r
