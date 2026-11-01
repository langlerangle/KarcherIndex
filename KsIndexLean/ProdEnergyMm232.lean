module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache23040

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm232 : Finset ℤ := Finset.Ioc (6655) (6719)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm232

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm232)

def idx (n : ℤ) : ℕ := (n - (6655)).toNat

lemma mem_wMm232 {n : ℤ} (hn : n ∈ wMm232) : (6655) < n ∧ n ≤ (6719) := by
  simpa only [wMm232, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm232) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm232 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm232) :
    2 * Cache23040.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm232 hn
  simp only [idx, Cache23040.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm232) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm232 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm232) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm232 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm232) :
    sampleNumerator (2 * n + 1) =
      (Cache23040.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache23040.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm232) :
    sampleRadius (2 * n + 1) =
      (Cache23040.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache23040.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm232_c_fast : tableEnergyNumerator t wMm232 4 1 = (433187209993749862187521830243213530345269650508909316754299691235379668215141219662313766334664 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm232 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm232 4 1 =
      ∑ n ∈ wMm232, ((6 * n + 4) ^ 2 - 4) *
        ((Cache23040.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm232_r_fast : tableEnergyRadius t wMm232 4 1 = (1339511682109606132455030879270106086190316378454465020712000486874406505079886609139508 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm232 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm232 4 1 =
      ∑ n ∈ wMm232, (|((6 * n + 4) ^ 2 - 4)| * (Cache23040.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache23040.entries[idx n]?.getD (0, 0)).1| +
          (Cache23040.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm232

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm232_c : tableEnergyNumerator t wMm232 4 1 = (433187209993749862187521830243213530345269650508909316754299691235379668215141219662313766334664 : ℤ) := by
  exact KsIndex.NegSignProdFastMm232.eMm232_c_fast
theorem eMm232_r : tableEnergyRadius t wMm232 4 1 = (1339511682109606132455030879270106086190316378454465020712000486874406505079886609139508 : ℤ) := by
  exact KsIndex.NegSignProdFastMm232.eMm232_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm232_c
#print axioms KsIndex.NegSignProd.eMm232_r
