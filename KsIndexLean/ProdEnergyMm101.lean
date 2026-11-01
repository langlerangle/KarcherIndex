module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache14592

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm101 : Finset ℤ := Finset.Ioc (-1729) (-1665)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm101

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm101)

def idx (n : ℤ) : ℕ := (n - (-1793)).toNat

lemma mem_wMm101 {n : ℤ} (hn : n ∈ wMm101) : (-1729) < n ∧ n ≤ (-1665) := by
  simpa only [wMm101, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm101) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm101 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm101) :
    2 * Cache14592.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm101 hn
  simp only [idx, Cache14592.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm101) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm101 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm101) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm101 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm101) :
    sampleNumerator (2 * n + 1) =
      (Cache14592.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache14592.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm101) :
    sampleRadius (2 * n + 1) =
      (Cache14592.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache14592.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm101_c_fast : tableEnergyNumerator t wMm101 4 1 = (366198070742054305951352230775896968087117153130060512320454845016970928602236864201538742769925 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm101 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm101 4 1 =
      ∑ n ∈ wMm101, ((6 * n + 4) ^ 2 - 4) *
        ((Cache14592.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm101_r_fast : tableEnergyRadius t wMm101 4 1 = (5112380150534422122027375075553643130702755801958534837668430994193120935748120565578418 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm101 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm101 4 1 =
      ∑ n ∈ wMm101, (|((6 * n + 4) ^ 2 - 4)| * (Cache14592.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache14592.entries[idx n]?.getD (0, 0)).1| +
          (Cache14592.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm101

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm101_c : tableEnergyNumerator t wMm101 4 1 = (366198070742054305951352230775896968087117153130060512320454845016970928602236864201538742769925 : ℤ) := by
  exact KsIndex.NegSignProdFastMm101.eMm101_c_fast
theorem eMm101_r : tableEnergyRadius t wMm101 4 1 = (5112380150534422122027375075553643130702755801958534837668430994193120935748120565578418 : ℤ) := by
  exact KsIndex.NegSignProdFastMm101.eMm101_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm101_c
#print axioms KsIndex.NegSignProd.eMm101_r
