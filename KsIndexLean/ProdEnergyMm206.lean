module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache21248

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm206 : Finset ℤ := Finset.Ioc (4991) (5055)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm206

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm206)

def idx (n : ℤ) : ℕ := (n - (4863)).toNat

lemma mem_wMm206 {n : ℤ} (hn : n ∈ wMm206) : (4991) < n ∧ n ≤ (5055) := by
  simpa only [wMm206, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm206) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm206 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm206) :
    2 * Cache21248.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm206 hn
  simp only [idx, Cache21248.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm206) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm206 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm206) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm206 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm206) :
    sampleNumerator (2 * n + 1) =
      (Cache21248.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache21248.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm206) :
    sampleRadius (2 * n + 1) =
      (Cache21248.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache21248.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm206_c_fast : tableEnergyNumerator t wMm206 4 1 = (758326967968425506574902850984091129446051302030900320876419876466502451554543784607574008942345 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm206 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm206 4 1 =
      ∑ n ∈ wMm206, ((6 * n + 4) ^ 2 - 4) *
        ((Cache21248.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm206_r_fast : tableEnergyRadius t wMm206 4 1 = (2383469643809202619335548444142332324595936208466608488120200051242859528383765763411135 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm206 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm206 4 1 =
      ∑ n ∈ wMm206, (|((6 * n + 4) ^ 2 - 4)| * (Cache21248.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache21248.entries[idx n]?.getD (0, 0)).1| +
          (Cache21248.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm206

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm206_c : tableEnergyNumerator t wMm206 4 1 = (758326967968425506574902850984091129446051302030900320876419876466502451554543784607574008942345 : ℤ) := by
  exact KsIndex.NegSignProdFastMm206.eMm206_c_fast
theorem eMm206_r : tableEnergyRadius t wMm206 4 1 = (2383469643809202619335548444142332324595936208466608488120200051242859528383765763411135 : ℤ) := by
  exact KsIndex.NegSignProdFastMm206.eMm206_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm206_c
#print axioms KsIndex.NegSignProd.eMm206_r
