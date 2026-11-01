module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache14080

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm93 : Finset ℤ := Finset.Ioc (-2241) (-2177)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm93

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm93)

def idx (n : ℤ) : ℕ := (n - (-2305)).toNat

lemma mem_wMm93 {n : ℤ} (hn : n ∈ wMm93) : (-2241) < n ∧ n ≤ (-2177) := by
  simpa only [wMm93, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm93) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm93 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm93) :
    2 * Cache14080.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm93 hn
  simp only [idx, Cache14080.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm93) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm93 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm93) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm93 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm93) :
    sampleNumerator (2 * n + 1) =
      (Cache14080.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache14080.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm93) :
    sampleRadius (2 * n + 1) =
      (Cache14080.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache14080.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm93_c_fast : tableEnergyNumerator t wMm93 4 1 = (249539409557170743142314524793107072017497029549530127562710802455144704197283983783550761609784 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm93 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm93 4 1 =
      ∑ n ∈ wMm93, ((6 * n + 4) ^ 2 - 4) *
        ((Cache14080.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm93_r_fast : tableEnergyRadius t wMm93 4 1 = (3208174403500885109997519631781060196572807136522658354602239400734053510696148111407469 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm93 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm93 4 1 =
      ∑ n ∈ wMm93, (|((6 * n + 4) ^ 2 - 4)| * (Cache14080.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache14080.entries[idx n]?.getD (0, 0)).1| +
          (Cache14080.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm93

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm93_c : tableEnergyNumerator t wMm93 4 1 = (249539409557170743142314524793107072017497029549530127562710802455144704197283983783550761609784 : ℤ) := by
  exact KsIndex.NegSignProdFastMm93.eMm93_c_fast
theorem eMm93_r : tableEnergyRadius t wMm93 4 1 = (3208174403500885109997519631781060196572807136522658354602239400734053510696148111407469 : ℤ) := by
  exact KsIndex.NegSignProdFastMm93.eMm93_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm93_c
#print axioms KsIndex.NegSignProd.eMm93_r
