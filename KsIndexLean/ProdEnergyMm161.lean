module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache18432

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm161 : Finset ℤ := Finset.Ioc (2111) (2175)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm161

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm161)

def idx (n : ℤ) : ℕ := (n - (2047)).toNat

lemma mem_wMm161 {n : ℤ} (hn : n ∈ wMm161) : (2111) < n ∧ n ≤ (2175) := by
  simpa only [wMm161, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm161) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm161 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm161) :
    2 * Cache18432.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm161 hn
  simp only [idx, Cache18432.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm161) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm161 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm161) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm161 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm161) :
    sampleNumerator (2 * n + 1) =
      (Cache18432.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache18432.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm161) :
    sampleRadius (2 * n + 1) =
      (Cache18432.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache18432.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm161_c_fast : tableEnergyNumerator t wMm161 4 1 = (4031655178158690900034404365507387295081309470123251341758532429862783577207445983997627683775697 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm161 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm161 4 1 =
      ∑ n ∈ wMm161, ((6 * n + 4) ^ 2 - 4) *
        ((Cache18432.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm161_r_fast : tableEnergyRadius t wMm161 4 1 = (13296471290216618242240462082116746177945029133174584579691865108831704936521596762267690 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm161 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm161 4 1 =
      ∑ n ∈ wMm161, (|((6 * n + 4) ^ 2 - 4)| * (Cache18432.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache18432.entries[idx n]?.getD (0, 0)).1| +
          (Cache18432.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm161

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm161_c : tableEnergyNumerator t wMm161 4 1 = (4031655178158690900034404365507387295081309470123251341758532429862783577207445983997627683775697 : ℤ) := by
  exact KsIndex.NegSignProdFastMm161.eMm161_c_fast
theorem eMm161_r : tableEnergyRadius t wMm161 4 1 = (13296471290216618242240462082116746177945029133174584579691865108831704936521596762267690 : ℤ) := by
  exact KsIndex.NegSignProdFastMm161.eMm161_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm161_c
#print axioms KsIndex.NegSignProd.eMm161_r
