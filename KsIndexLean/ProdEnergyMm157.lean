module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache18176

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm157 : Finset ℤ := Finset.Ioc (1855) (1919)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm157

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm157)

def idx (n : ℤ) : ℕ := (n - (1791)).toNat

lemma mem_wMm157 {n : ℤ} (hn : n ∈ wMm157) : (1855) < n ∧ n ≤ (1919) := by
  simpa only [wMm157, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm157) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm157 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm157) :
    2 * Cache18176.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm157 hn
  simp only [idx, Cache18176.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm157) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm157 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm157) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm157 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm157) :
    sampleNumerator (2 * n + 1) =
      (Cache18176.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache18176.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm157) :
    sampleRadius (2 * n + 1) =
      (Cache18176.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache18176.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm157_c_fast : tableEnergyNumerator t wMm157 4 1 = (5176974215890289886389750869938773105143814653495819547306450435334641035784560864720361260241724 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm157 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm157 4 1 =
      ∑ n ∈ wMm157, ((6 * n + 4) ^ 2 - 4) *
        ((Cache18176.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm157_r_fast : tableEnergyRadius t wMm157 4 1 = (17195844422182898591968765823029396576263044049621415118590122205333881204797744506280084 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm157 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm157 4 1 =
      ∑ n ∈ wMm157, (|((6 * n + 4) ^ 2 - 4)| * (Cache18176.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache18176.entries[idx n]?.getD (0, 0)).1| +
          (Cache18176.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm157

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm157_c : tableEnergyNumerator t wMm157 4 1 = (5176974215890289886389750869938773105143814653495819547306450435334641035784560864720361260241724 : ℤ) := by
  exact KsIndex.NegSignProdFastMm157.eMm157_c_fast
theorem eMm157_r : tableEnergyRadius t wMm157 4 1 = (17195844422182898591968765823029396576263044049621415118590122205333881204797744506280084 : ℤ) := by
  exact KsIndex.NegSignProdFastMm157.eMm157_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm157_c
#print axioms KsIndex.NegSignProd.eMm157_r
