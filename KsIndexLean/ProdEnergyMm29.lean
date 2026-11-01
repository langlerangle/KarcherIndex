module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache9984

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm29 : Finset ℤ := Finset.Ioc (-6337) (-6273)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm29

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm29)

def idx (n : ℤ) : ℕ := (n - (-6401)).toNat

lemma mem_wMm29 {n : ℤ} (hn : n ∈ wMm29) : (-6337) < n ∧ n ≤ (-6273) := by
  simpa only [wMm29, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm29) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm29 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm29) :
    2 * Cache9984.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm29 hn
  simp only [idx, Cache9984.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm29) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm29 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm29) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm29 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm29) :
    sampleNumerator (2 * n + 1) =
      (Cache9984.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache9984.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm29) :
    sampleRadius (2 * n + 1) =
      (Cache9984.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache9984.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm29_c_fast : tableEnergyNumerator t wMm29 4 1 = (50142688351837107251612558668861652258110653974533581262223900877634438169674947797805492949641 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm29 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm29 4 1 =
      ∑ n ∈ wMm29, ((6 * n + 4) ^ 2 - 4) *
        ((Cache9984.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm29_r_fast : tableEnergyRadius t wMm29 4 1 = (484491196251092616202488292199403796031544911176967957933439696951458037406339336146716 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm29 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm29 4 1 =
      ∑ n ∈ wMm29, (|((6 * n + 4) ^ 2 - 4)| * (Cache9984.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache9984.entries[idx n]?.getD (0, 0)).1| +
          (Cache9984.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm29

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm29_c : tableEnergyNumerator t wMm29 4 1 = (50142688351837107251612558668861652258110653974533581262223900877634438169674947797805492949641 : ℤ) := by
  exact KsIndex.NegSignProdFastMm29.eMm29_c_fast
theorem eMm29_r : tableEnergyRadius t wMm29 4 1 = (484491196251092616202488292199403796031544911176967957933439696951458037406339336146716 : ℤ) := by
  exact KsIndex.NegSignProdFastMm29.eMm29_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm29_c
#print axioms KsIndex.NegSignProd.eMm29_r
