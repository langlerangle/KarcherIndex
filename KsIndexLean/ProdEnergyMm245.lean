module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache23808

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm245 : Finset ℤ := Finset.Ioc (7487) (7551)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm245

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm245)

def idx (n : ℤ) : ℕ := (n - (7423)).toNat

lemma mem_wMm245 {n : ℤ} (hn : n ∈ wMm245) : (7487) < n ∧ n ≤ (7551) := by
  simpa only [wMm245, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm245) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm245 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm245) :
    2 * Cache23808.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm245 hn
  simp only [idx, Cache23808.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm245) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm245 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm245) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm245 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm245) :
    sampleNumerator (2 * n + 1) =
      (Cache23808.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache23808.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm245) :
    sampleRadius (2 * n + 1) =
      (Cache23808.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache23808.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm245_c_fast : tableEnergyNumerator t wMm245 4 1 = (344424751979763736520754125476798572997348193529087077519345945045706247596656674371160847798356 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm245 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm245 4 1 =
      ∑ n ∈ wMm245, ((6 * n + 4) ^ 2 - 4) *
        ((Cache23808.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm245_r_fast : tableEnergyRadius t wMm245 4 1 = (1057925805211172656235185576402701911849668368936376656301870614573223063347599300282671 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm245 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm245 4 1 =
      ∑ n ∈ wMm245, (|((6 * n + 4) ^ 2 - 4)| * (Cache23808.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache23808.entries[idx n]?.getD (0, 0)).1| +
          (Cache23808.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm245

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm245_c : tableEnergyNumerator t wMm245 4 1 = (344424751979763736520754125476798572997348193529087077519345945045706247596656674371160847798356 : ℤ) := by
  exact KsIndex.NegSignProdFastMm245.eMm245_c_fast
theorem eMm245_r : tableEnergyRadius t wMm245 4 1 = (1057925805211172656235185576402701911849668368936376656301870614573223063347599300282671 : ℤ) := by
  exact KsIndex.NegSignProdFastMm245.eMm245_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm245_c
#print axioms KsIndex.NegSignProd.eMm245_r
