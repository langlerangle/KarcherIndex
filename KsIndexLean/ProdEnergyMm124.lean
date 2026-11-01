module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache16128

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm124 : Finset ℤ := Finset.Ioc (-257) (-193)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm124

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm124)

def idx (n : ℤ) : ℕ := (n - (-257)).toNat

lemma mem_wMm124 {n : ℤ} (hn : n ∈ wMm124) : (-257) < n ∧ n ≤ (-193) := by
  simpa only [wMm124, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm124) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm124 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm124) :
    2 * Cache16128.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm124 hn
  simp only [idx, Cache16128.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm124) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm124 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm124) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm124 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm124) :
    sampleNumerator (2 * n + 1) =
      (Cache16128.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache16128.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm124) :
    sampleRadius (2 * n + 1) =
      (Cache16128.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache16128.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm124_c_fast : tableEnergyNumerator t wMm124 4 1 = (3991706038527683249231253789155356633087333536453483245635011056192467192404919279824197326837422 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm124 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm124 4 1 =
      ∑ n ∈ wMm124, ((6 * n + 4) ^ 2 - 4) *
        ((Cache16128.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm124_r_fast : tableEnergyRadius t wMm124 4 1 = (140503471461763507398255617422731601934616583843132866700112209868994165926631547196946737 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm124 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm124 4 1 =
      ∑ n ∈ wMm124, (|((6 * n + 4) ^ 2 - 4)| * (Cache16128.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache16128.entries[idx n]?.getD (0, 0)).1| +
          (Cache16128.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm124

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm124_c : tableEnergyNumerator t wMm124 4 1 = (3991706038527683249231253789155356633087333536453483245635011056192467192404919279824197326837422 : ℤ) := by
  exact KsIndex.NegSignProdFastMm124.eMm124_c_fast
theorem eMm124_r : tableEnergyRadius t wMm124 4 1 = (140503471461763507398255617422731601934616583843132866700112209868994165926631547196946737 : ℤ) := by
  exact KsIndex.NegSignProdFastMm124.eMm124_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm124_c
#print axioms KsIndex.NegSignProd.eMm124_r
