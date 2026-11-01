module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache15872

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm121 : Finset ℤ := Finset.Ioc (-449) (-385)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm121

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm121)

def idx (n : ℤ) : ℕ := (n - (-513)).toNat

lemma mem_wMm121 {n : ℤ} (hn : n ∈ wMm121) : (-449) < n ∧ n ≤ (-385) := by
  simpa only [wMm121, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm121) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm121 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm121) :
    2 * Cache15872.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm121 hn
  simp only [idx, Cache15872.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm121) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm121 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm121) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm121 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm121) :
    sampleNumerator (2 * n + 1) =
      (Cache15872.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache15872.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm121) :
    sampleRadius (2 * n + 1) =
      (Cache15872.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache15872.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm121_c_fast : tableEnergyNumerator t wMm121 4 1 = (2244709525612882358862157017420280046942153307142179985625719226243484178832474047294323757233252 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm121 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm121 4 1 =
      ∑ n ∈ wMm121, ((6 * n + 4) ^ 2 - 4) *
        ((Cache15872.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm121_r_fast : tableEnergyRadius t wMm121 4 1 = (54846274651683982417557737438223883513619928160303891961134807160889407636353068090244485 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm121 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm121 4 1 =
      ∑ n ∈ wMm121, (|((6 * n + 4) ^ 2 - 4)| * (Cache15872.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache15872.entries[idx n]?.getD (0, 0)).1| +
          (Cache15872.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm121

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm121_c : tableEnergyNumerator t wMm121 4 1 = (2244709525612882358862157017420280046942153307142179985625719226243484178832474047294323757233252 : ℤ) := by
  exact KsIndex.NegSignProdFastMm121.eMm121_c_fast
theorem eMm121_r : tableEnergyRadius t wMm121 4 1 = (54846274651683982417557737438223883513619928160303891961134807160889407636353068090244485 : ℤ) := by
  exact KsIndex.NegSignProdFastMm121.eMm121_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm121_c
#print axioms KsIndex.NegSignProd.eMm121_r
