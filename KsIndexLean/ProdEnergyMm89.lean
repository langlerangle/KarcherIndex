module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache13824

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm89 : Finset ℤ := Finset.Ioc (-2497) (-2433)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm89

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm89)

def idx (n : ℤ) : ℕ := (n - (-2561)).toNat

lemma mem_wMm89 {n : ℤ} (hn : n ∈ wMm89) : (-2497) < n ∧ n ≤ (-2433) := by
  simpa only [wMm89, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm89) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm89 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm89) :
    2 * Cache13824.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm89 hn
  simp only [idx, Cache13824.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm89) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm89 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm89) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm89 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm89) :
    sampleNumerator (2 * n + 1) =
      (Cache13824.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache13824.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm89) :
    sampleRadius (2 * n + 1) =
      (Cache13824.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache13824.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm89_c_fast : tableEnergyNumerator t wMm89 4 1 = (212169684270525923684188801506232553204169026237042851818186093100410847295781229993841192630032 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm89 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm89 4 1 =
      ∑ n ∈ wMm89, ((6 * n + 4) ^ 2 - 4) *
        ((Cache13824.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm89_r_fast : tableEnergyRadius t wMm89 4 1 = (2639654271048832056267779731584215761426521001232984293043093871815934428362594439771808 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm89 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm89 4 1 =
      ∑ n ∈ wMm89, (|((6 * n + 4) ^ 2 - 4)| * (Cache13824.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache13824.entries[idx n]?.getD (0, 0)).1| +
          (Cache13824.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm89

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm89_c : tableEnergyNumerator t wMm89 4 1 = (212169684270525923684188801506232553204169026237042851818186093100410847295781229993841192630032 : ℤ) := by
  exact KsIndex.NegSignProdFastMm89.eMm89_c_fast
theorem eMm89_r : tableEnergyRadius t wMm89 4 1 = (2639654271048832056267779731584215761426521001232984293043093871815934428362594439771808 : ℤ) := by
  exact KsIndex.NegSignProdFastMm89.eMm89_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm89_c
#print axioms KsIndex.NegSignProd.eMm89_r
