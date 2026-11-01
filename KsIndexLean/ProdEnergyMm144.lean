module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache17408

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm144 : Finset ℤ := Finset.Ioc (1023) (1087)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm144

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm144)

def idx (n : ℤ) : ℕ := (n - (1023)).toNat

lemma mem_wMm144 {n : ℤ} (hn : n ∈ wMm144) : (1023) < n ∧ n ≤ (1087) := by
  simpa only [wMm144, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm144) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm144 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm144) :
    2 * Cache17408.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm144 hn
  simp only [idx, Cache17408.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm144) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm144 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm144) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm144 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm144) :
    sampleNumerator (2 * n + 1) =
      (Cache17408.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache17408.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm144) :
    sampleRadius (2 * n + 1) =
      (Cache17408.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache17408.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm144_c_fast : tableEnergyNumerator t wMm144 4 1 = (16262121735196241082181050599159228611957395818877738800751385451293322046316965899619740485623991 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm144 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm144 4 1 =
      ∑ n ∈ wMm144, ((6 * n + 4) ^ 2 - 4) *
        ((Cache17408.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm144_r_fast : tableEnergyRadius t wMm144 4 1 = (55791858011629549004986427141310136969063282345126207040749120784339128909424591770281573 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm144 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm144 4 1 =
      ∑ n ∈ wMm144, (|((6 * n + 4) ^ 2 - 4)| * (Cache17408.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache17408.entries[idx n]?.getD (0, 0)).1| +
          (Cache17408.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm144

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm144_c : tableEnergyNumerator t wMm144 4 1 = (16262121735196241082181050599159228611957395818877738800751385451293322046316965899619740485623991 : ℤ) := by
  exact KsIndex.NegSignProdFastMm144.eMm144_c_fast
theorem eMm144_r : tableEnergyRadius t wMm144 4 1 = (55791858011629549004986427141310136969063282345126207040749120784339128909424591770281573 : ℤ) := by
  exact KsIndex.NegSignProdFastMm144.eMm144_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm144_c
#print axioms KsIndex.NegSignProd.eMm144_r
