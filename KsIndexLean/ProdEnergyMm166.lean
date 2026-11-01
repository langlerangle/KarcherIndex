module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache18688

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm166 : Finset ℤ := Finset.Ioc (2431) (2495)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm166

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm166)

def idx (n : ℤ) : ℕ := (n - (2303)).toNat

lemma mem_wMm166 {n : ℤ} (hn : n ∈ wMm166) : (2431) < n ∧ n ≤ (2495) := by
  simpa only [wMm166, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm166) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm166 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm166) :
    2 * Cache18688.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm166 hn
  simp only [idx, Cache18688.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm166) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm166 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm166) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm166 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm166) :
    sampleNumerator (2 * n + 1) =
      (Cache18688.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache18688.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm166) :
    sampleRadius (2 * n + 1) =
      (Cache18688.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache18688.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm166_c_fast : tableEnergyNumerator t wMm166 4 1 = (3067277278139279723216687766550472042842024030516556354638163359243571519221925029599027210073406 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm166 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm166 4 1 =
      ∑ n ∈ wMm166, ((6 * n + 4) ^ 2 - 4) *
        ((Cache18688.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm166_r_fast : tableEnergyRadius t wMm166 4 1 = (10037193807169162799695047999715659635402025239834238125651475824171700583705658441901584 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm166 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm166 4 1 =
      ∑ n ∈ wMm166, (|((6 * n + 4) ^ 2 - 4)| * (Cache18688.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache18688.entries[idx n]?.getD (0, 0)).1| +
          (Cache18688.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm166

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm166_c : tableEnergyNumerator t wMm166 4 1 = (3067277278139279723216687766550472042842024030516556354638163359243571519221925029599027210073406 : ℤ) := by
  exact KsIndex.NegSignProdFastMm166.eMm166_c_fast
theorem eMm166_r : tableEnergyRadius t wMm166 4 1 = (10037193807169162799695047999715659635402025239834238125651475824171700583705658441901584 : ℤ) := by
  exact KsIndex.NegSignProdFastMm166.eMm166_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm166_c
#print axioms KsIndex.NegSignProd.eMm166_r
