module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache23296

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm238 : Finset ℤ := Finset.Ioc (7039) (7103)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm238

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm238)

def idx (n : ℤ) : ℕ := (n - (6911)).toNat

lemma mem_wMm238 {n : ℤ} (hn : n ∈ wMm238) : (7039) < n ∧ n ≤ (7103) := by
  simpa only [wMm238, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm238) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm238 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm238) :
    2 * Cache23296.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm238 hn
  simp only [idx, Cache23296.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm238) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm238 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm238) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm238 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm238) :
    sampleNumerator (2 * n + 1) =
      (Cache23296.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache23296.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm238) :
    sampleRadius (2 * n + 1) =
      (Cache23296.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache23296.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm238_c_fast : tableEnergyNumerator t wMm238 4 1 = (388377923144431157824963916983712600568669273726467329507332158900110815499807262442217944729554 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm238 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm238 4 1 =
      ∑ n ∈ wMm238, ((6 * n + 4) ^ 2 - 4) *
        ((Cache23296.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm238_r_fast : tableEnergyRadius t wMm238 4 1 = (1197127294861110181990022322745609806272549829269203291617177003070025490795623672747770 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm238 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm238 4 1 =
      ∑ n ∈ wMm238, (|((6 * n + 4) ^ 2 - 4)| * (Cache23296.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache23296.entries[idx n]?.getD (0, 0)).1| +
          (Cache23296.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm238

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm238_c : tableEnergyNumerator t wMm238 4 1 = (388377923144431157824963916983712600568669273726467329507332158900110815499807262442217944729554 : ℤ) := by
  exact KsIndex.NegSignProdFastMm238.eMm238_c_fast
theorem eMm238_r : tableEnergyRadius t wMm238 4 1 = (1197127294861110181990022322745609806272549829269203291617177003070025490795623672747770 : ℤ) := by
  exact KsIndex.NegSignProdFastMm238.eMm238_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm238_c
#print axioms KsIndex.NegSignProd.eMm238_r
