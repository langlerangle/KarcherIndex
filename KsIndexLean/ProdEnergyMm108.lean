module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache15104

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm108 : Finset ℤ := Finset.Ioc (-1281) (-1217)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm108

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm108)

def idx (n : ℤ) : ℕ := (n - (-1281)).toNat

lemma mem_wMm108 {n : ℤ} (hn : n ∈ wMm108) : (-1281) < n ∧ n ≤ (-1217) := by
  simpa only [wMm108, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm108) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm108 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm108) :
    2 * Cache15104.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm108 hn
  simp only [idx, Cache15104.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm108) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm108 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm108) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm108 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm108) :
    sampleNumerator (2 * n + 1) =
      (Cache15104.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache15104.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm108) :
    sampleRadius (2 * n + 1) =
      (Cache15104.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache15104.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm108_c_fast : tableEnergyNumerator t wMm108 4 1 = (564451741976648714321407372700228230840981143757473538507858417664837083107950998667911635948214 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm108 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm108 4 1 =
      ∑ n ∈ wMm108, ((6 * n + 4) ^ 2 - 4) *
        ((Cache15104.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm108_r_fast : tableEnergyRadius t wMm108 4 1 = (8733086269968888927766469792949511243817345549889130362492554628262093959935867679313942 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm108 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm108 4 1 =
      ∑ n ∈ wMm108, (|((6 * n + 4) ^ 2 - 4)| * (Cache15104.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache15104.entries[idx n]?.getD (0, 0)).1| +
          (Cache15104.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm108

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm108_c : tableEnergyNumerator t wMm108 4 1 = (564451741976648714321407372700228230840981143757473538507858417664837083107950998667911635948214 : ℤ) := by
  exact KsIndex.NegSignProdFastMm108.eMm108_c_fast
theorem eMm108_r : tableEnergyRadius t wMm108 4 1 = (8733086269968888927766469792949511243817345549889130362492554628262093959935867679313942 : ℤ) := by
  exact KsIndex.NegSignProdFastMm108.eMm108_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm108_c
#print axioms KsIndex.NegSignProd.eMm108_r
