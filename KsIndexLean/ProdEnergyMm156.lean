module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache18176

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm156 : Finset ℤ := Finset.Ioc (1791) (1855)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm156

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm156)

def idx (n : ℤ) : ℕ := (n - (1791)).toNat

lemma mem_wMm156 {n : ℤ} (hn : n ∈ wMm156) : (1791) < n ∧ n ≤ (1855) := by
  simpa only [wMm156, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm156) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm156 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm156) :
    2 * Cache18176.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm156 hn
  simp only [idx, Cache18176.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm156) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm156 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm156) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm156 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm156) :
    sampleNumerator (2 * n + 1) =
      (Cache18176.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache18176.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm156) :
    sampleRadius (2 * n + 1) =
      (Cache18176.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache18176.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm156_c_fast : tableEnergyNumerator t wMm156 4 1 = (5540375341537565992018729133747878133679056226619228720634428723980164615367439429390012019044681 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm156 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm156 4 1 =
      ∑ n ∈ wMm156, ((6 * n + 4) ^ 2 - 4) *
        ((Cache18176.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm156_r_fast : tableEnergyRadius t wMm156 4 1 = (18438462216776323446206856773322332681560270201518130231087461877250650034089777626469746 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm156 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm156 4 1 =
      ∑ n ∈ wMm156, (|((6 * n + 4) ^ 2 - 4)| * (Cache18176.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache18176.entries[idx n]?.getD (0, 0)).1| +
          (Cache18176.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm156

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm156_c : tableEnergyNumerator t wMm156 4 1 = (5540375341537565992018729133747878133679056226619228720634428723980164615367439429390012019044681 : ℤ) := by
  exact KsIndex.NegSignProdFastMm156.eMm156_c_fast
theorem eMm156_r : tableEnergyRadius t wMm156 4 1 = (18438462216776323446206856773322332681560270201518130231087461877250650034089777626469746 : ℤ) := by
  exact KsIndex.NegSignProdFastMm156.eMm156_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm156_c
#print axioms KsIndex.NegSignProd.eMm156_r
