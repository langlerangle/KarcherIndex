module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache18944

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm170 : Finset ℤ := Finset.Ioc (2687) (2751)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm170

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm170)

def idx (n : ℤ) : ℕ := (n - (2559)).toNat

lemma mem_wMm170 {n : ℤ} (hn : n ∈ wMm170) : (2687) < n ∧ n ≤ (2751) := by
  simpa only [wMm170, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm170) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm170 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm170) :
    2 * Cache18944.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm170 hn
  simp only [idx, Cache18944.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm170) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm170 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm170) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm170 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm170) :
    sampleNumerator (2 * n + 1) =
      (Cache18944.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache18944.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm170) :
    sampleRadius (2 * n + 1) =
      (Cache18944.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache18944.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm170_c_fast : tableEnergyNumerator t wMm170 4 1 = (2526015325180216616064250190484169916806903641025108590782822278932764719064819602787475232718517 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm170 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm170 4 1 =
      ∑ n ∈ wMm170, ((6 * n + 4) ^ 2 - 4) *
        ((Cache18944.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm170_r_fast : tableEnergyRadius t wMm170 4 1 = (8220130563530080044922688010824767845116024839567839819737370297963814004027907315269087 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm170 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm170 4 1 =
      ∑ n ∈ wMm170, (|((6 * n + 4) ^ 2 - 4)| * (Cache18944.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache18944.entries[idx n]?.getD (0, 0)).1| +
          (Cache18944.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm170

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm170_c : tableEnergyNumerator t wMm170 4 1 = (2526015325180216616064250190484169916806903641025108590782822278932764719064819602787475232718517 : ℤ) := by
  exact KsIndex.NegSignProdFastMm170.eMm170_c_fast
theorem eMm170_r : tableEnergyRadius t wMm170 4 1 = (8220130563530080044922688010824767845116024839567839819737370297963814004027907315269087 : ℤ) := by
  exact KsIndex.NegSignProdFastMm170.eMm170_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm170_c
#print axioms KsIndex.NegSignProd.eMm170_r
