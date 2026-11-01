module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache11520

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm52 : Finset ℤ := Finset.Ioc (-4865) (-4801)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm52

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm52)

def idx (n : ℤ) : ℕ := (n - (-4865)).toNat

lemma mem_wMm52 {n : ℤ} (hn : n ∈ wMm52) : (-4865) < n ∧ n ≤ (-4801) := by
  simpa only [wMm52, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm52) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm52 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm52) :
    2 * Cache11520.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm52 hn
  simp only [idx, Cache11520.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm52) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm52 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm52) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm52 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm52) :
    sampleNumerator (2 * n + 1) =
      (Cache11520.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache11520.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm52) :
    sampleRadius (2 * n + 1) =
      (Cache11520.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache11520.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm52_c_fast : tableEnergyNumerator t wMm52 4 1 = (76078185342588431069436905230227788853450342023145924210513372520636160042067219780601273220650 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm52 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm52 4 1 =
      ∑ n ∈ wMm52, ((6 * n + 4) ^ 2 - 4) *
        ((Cache11520.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm52_r_fast : tableEnergyRadius t wMm52 4 1 = (786015517054444069323465073003652171067128847727611036652350979562890195362638797782485 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm52 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm52 4 1 =
      ∑ n ∈ wMm52, (|((6 * n + 4) ^ 2 - 4)| * (Cache11520.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache11520.entries[idx n]?.getD (0, 0)).1| +
          (Cache11520.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm52

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm52_c : tableEnergyNumerator t wMm52 4 1 = (76078185342588431069436905230227788853450342023145924210513372520636160042067219780601273220650 : ℤ) := by
  exact KsIndex.NegSignProdFastMm52.eMm52_c_fast
theorem eMm52_r : tableEnergyRadius t wMm52 4 1 = (786015517054444069323465073003652171067128847727611036652350979562890195362638797782485 : ℤ) := by
  exact KsIndex.NegSignProdFastMm52.eMm52_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm52_c
#print axioms KsIndex.NegSignProd.eMm52_r
