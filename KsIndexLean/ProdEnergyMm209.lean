module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache21504

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm209 : Finset ℤ := Finset.Ioc (5183) (5247)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm209

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm209)

def idx (n : ℤ) : ℕ := (n - (5119)).toNat

lemma mem_wMm209 {n : ℤ} (hn : n ∈ wMm209) : (5183) < n ∧ n ≤ (5247) := by
  simpa only [wMm209, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm209) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm209 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm209) :
    2 * Cache21504.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm209 hn
  simp only [idx, Cache21504.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm209) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm209 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm209) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm209 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm209) :
    sampleNumerator (2 * n + 1) =
      (Cache21504.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache21504.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm209) :
    sampleRadius (2 * n + 1) =
      (Cache21504.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache21504.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm209_c_fast : tableEnergyNumerator t wMm209 4 1 = (704628504409521980391314618728600225674278681226420012101028535840317146304121468194999245207205 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm209 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm209 4 1 =
      ∑ n ∈ wMm209, ((6 * n + 4) ^ 2 - 4) *
        ((Cache21504.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm209_r_fast : tableEnergyRadius t wMm209 4 1 = (2209970333298298909896928726532550677435269053804138692511734498706244673877110184908720 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm209 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm209 4 1 =
      ∑ n ∈ wMm209, (|((6 * n + 4) ^ 2 - 4)| * (Cache21504.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache21504.entries[idx n]?.getD (0, 0)).1| +
          (Cache21504.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm209

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm209_c : tableEnergyNumerator t wMm209 4 1 = (704628504409521980391314618728600225674278681226420012101028535840317146304121468194999245207205 : ℤ) := by
  exact KsIndex.NegSignProdFastMm209.eMm209_c_fast
theorem eMm209_r : tableEnergyRadius t wMm209 4 1 = (2209970333298298909896928726532550677435269053804138692511734498706244673877110184908720 : ℤ) := by
  exact KsIndex.NegSignProdFastMm209.eMm209_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm209_c
#print axioms KsIndex.NegSignProd.eMm209_r
