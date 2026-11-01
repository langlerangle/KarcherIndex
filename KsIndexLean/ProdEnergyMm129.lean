module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache16384

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm129 : Finset ℤ := Finset.Ioc (63) (127)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm129

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm129)

def idx (n : ℤ) : ℕ := (n - (-1)).toNat

lemma mem_wMm129 {n : ℤ} (hn : n ∈ wMm129) : (63) < n ∧ n ≤ (127) := by
  simpa only [wMm129, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm129) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm129 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm129) :
    2 * Cache16384.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm129 hn
  simp only [idx, Cache16384.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm129) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm129 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm129) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm129 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm129) :
    sampleNumerator (2 * n + 1) =
      (Cache16384.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache16384.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm129) :
    sampleRadius (2 * n + 1) =
      (Cache16384.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache16384.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm129_c_fast : tableEnergyNumerator t wMm129 4 1 = (2109974820828840769742162328800123598697049395196012855949453147539004958434189765218066813838475231 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm129 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm129 4 1 =
      ∑ n ∈ wMm129, ((6 * n + 4) ^ 2 - 4) *
        ((Cache16384.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm129_r_fast : tableEnergyRadius t wMm129 4 1 = (8287402612391494534506234562778593631940044631652876659371919492484845575087479641741052248 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm129 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm129 4 1 =
      ∑ n ∈ wMm129, (|((6 * n + 4) ^ 2 - 4)| * (Cache16384.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache16384.entries[idx n]?.getD (0, 0)).1| +
          (Cache16384.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm129

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm129_c : tableEnergyNumerator t wMm129 4 1 = (2109974820828840769742162328800123598697049395196012855949453147539004958434189765218066813838475231 : ℤ) := by
  exact KsIndex.NegSignProdFastMm129.eMm129_c_fast
theorem eMm129_r : tableEnergyRadius t wMm129 4 1 = (8287402612391494534506234562778593631940044631652876659371919492484845575087479641741052248 : ℤ) := by
  exact KsIndex.NegSignProdFastMm129.eMm129_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm129_c
#print axioms KsIndex.NegSignProd.eMm129_r
