module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache17152

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm141 : Finset ℤ := Finset.Ioc (831) (895)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm141

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm141)

def idx (n : ℤ) : ℕ := (n - (767)).toNat

lemma mem_wMm141 {n : ℤ} (hn : n ∈ wMm141) : (831) < n ∧ n ≤ (895) := by
  simpa only [wMm141, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm141) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm141 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm141) :
    2 * Cache17152.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm141 hn
  simp only [idx, Cache17152.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm141) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm141 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm141) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm141 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm141) :
    sampleNumerator (2 * n + 1) =
      (Cache17152.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache17152.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm141) :
    sampleRadius (2 * n + 1) =
      (Cache17152.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache17152.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm141_c_fast : tableEnergyNumerator t wMm141 4 1 = (24168357842717736445793801582106215968689628605866572093168210471375640496354810714935053014569096 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm141 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm141 4 1 =
      ∑ n ∈ wMm141, ((6 * n + 4) ^ 2 - 4) *
        ((Cache17152.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm141_r_fast : tableEnergyRadius t wMm141 4 1 = (83841035625362989468694628112287046571470258509692322721572262510081392570744616141556149 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm141 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm141 4 1 =
      ∑ n ∈ wMm141, (|((6 * n + 4) ^ 2 - 4)| * (Cache17152.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache17152.entries[idx n]?.getD (0, 0)).1| +
          (Cache17152.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm141

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm141_c : tableEnergyNumerator t wMm141 4 1 = (24168357842717736445793801582106215968689628605866572093168210471375640496354810714935053014569096 : ℤ) := by
  exact KsIndex.NegSignProdFastMm141.eMm141_c_fast
theorem eMm141_r : tableEnergyRadius t wMm141 4 1 = (83841035625362989468694628112287046571470258509692322721572262510081392570744616141556149 : ℤ) := by
  exact KsIndex.NegSignProdFastMm141.eMm141_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm141_c
#print axioms KsIndex.NegSignProd.eMm141_r
