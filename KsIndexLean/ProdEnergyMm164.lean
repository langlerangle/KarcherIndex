module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache18688

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm164 : Finset ℤ := Finset.Ioc (2303) (2367)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm164

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm164)

def idx (n : ℤ) : ℕ := (n - (2303)).toNat

lemma mem_wMm164 {n : ℤ} (hn : n ∈ wMm164) : (2303) < n ∧ n ≤ (2367) := by
  simpa only [wMm164, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm164) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm164 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm164) :
    2 * Cache18688.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm164 hn
  simp only [idx, Cache18688.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm164) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm164 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm164) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm164 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm164) :
    sampleNumerator (2 * n + 1) =
      (Cache18688.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache18688.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm164) :
    sampleRadius (2 * n + 1) =
      (Cache18688.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache18688.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm164_c_fast : tableEnergyNumerator t wMm164 4 1 = (3406229046248579458388622773341573433757006590217835500800320617506312885397725901306168139963534 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm164 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm164 4 1 =
      ∑ n ∈ wMm164, ((6 * n + 4) ^ 2 - 4) *
        ((Cache18688.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm164_r_fast : tableEnergyRadius t wMm164 4 1 = (11179838714774885847877955968448336655417351575162094017108624821320714757270318939659085 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm164 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm164 4 1 =
      ∑ n ∈ wMm164, (|((6 * n + 4) ^ 2 - 4)| * (Cache18688.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache18688.entries[idx n]?.getD (0, 0)).1| +
          (Cache18688.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm164

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm164_c : tableEnergyNumerator t wMm164 4 1 = (3406229046248579458388622773341573433757006590217835500800320617506312885397725901306168139963534 : ℤ) := by
  exact KsIndex.NegSignProdFastMm164.eMm164_c_fast
theorem eMm164_r : tableEnergyRadius t wMm164 4 1 = (11179838714774885847877955968448336655417351575162094017108624821320714757270318939659085 : ℤ) := by
  exact KsIndex.NegSignProdFastMm164.eMm164_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm164_c
#print axioms KsIndex.NegSignProd.eMm164_r
