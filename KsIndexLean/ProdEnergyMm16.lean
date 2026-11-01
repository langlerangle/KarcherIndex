module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache9216

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm16 : Finset ℤ := Finset.Ioc (-7169) (-7105)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm16

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm16)

def idx (n : ℤ) : ℕ := (n - (-7169)).toNat

lemma mem_wMm16 {n : ℤ} (hn : n ∈ wMm16) : (-7169) < n ∧ n ≤ (-7105) := by
  simpa only [wMm16, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm16) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm16 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm16) :
    2 * Cache9216.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm16 hn
  simp only [idx, Cache9216.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm16) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm16 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm16) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm16 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm16) :
    sampleNumerator (2 * n + 1) =
      (Cache9216.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache9216.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm16) :
    sampleRadius (2 * n + 1) =
      (Cache9216.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache9216.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm16_c_fast : tableEnergyNumerator t wMm16 4 1 = (41205199221753420521134262432775084037851130918562714900906569202399845807312039483379701471370 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm16 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm16 4 1 =
      ∑ n ∈ wMm16, ((6 * n + 4) ^ 2 - 4) *
        ((Cache9216.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm16_r_fast : tableEnergyRadius t wMm16 4 1 = (386304340973381923404376722936694981500989086078342301554859013715926916062152873197049 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm16 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm16 4 1 =
      ∑ n ∈ wMm16, (|((6 * n + 4) ^ 2 - 4)| * (Cache9216.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache9216.entries[idx n]?.getD (0, 0)).1| +
          (Cache9216.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm16

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm16_c : tableEnergyNumerator t wMm16 4 1 = (41205199221753420521134262432775084037851130918562714900906569202399845807312039483379701471370 : ℤ) := by
  exact KsIndex.NegSignProdFastMm16.eMm16_c_fast
theorem eMm16_r : tableEnergyRadius t wMm16 4 1 = (386304340973381923404376722936694981500989086078342301554859013715926916062152873197049 : ℤ) := by
  exact KsIndex.NegSignProdFastMm16.eMm16_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm16_c
#print axioms KsIndex.NegSignProd.eMm16_r
