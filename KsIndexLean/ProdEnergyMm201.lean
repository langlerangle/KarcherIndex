module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache20992

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm201 : Finset ℤ := Finset.Ioc (4671) (4735)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm201

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm201)

def idx (n : ℤ) : ℕ := (n - (4607)).toNat

lemma mem_wMm201 {n : ℤ} (hn : n ∈ wMm201) : (4671) < n ∧ n ≤ (4735) := by
  simpa only [wMm201, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm201) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm201 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm201) :
    2 * Cache20992.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm201 hn
  simp only [idx, Cache20992.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm201) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm201 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm201) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm201 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm201) :
    sampleNumerator (2 * n + 1) =
      (Cache20992.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache20992.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm201) :
    sampleRadius (2 * n + 1) =
      (Cache20992.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache20992.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm201_c_fast : tableEnergyNumerator t wMm201 4 1 = (862662464294692446564098411909788991875514061398791428219290409786997750112959828859612008333558 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm201 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm201 4 1 =
      ∑ n ∈ wMm201, ((6 * n + 4) ^ 2 - 4) *
        ((Cache20992.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm201_r_fast : tableEnergyRadius t wMm201 4 1 = (2721569020001682341459494172044225401804364854616512751464856937754447986447666916819041 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm201 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm201 4 1 =
      ∑ n ∈ wMm201, (|((6 * n + 4) ^ 2 - 4)| * (Cache20992.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache20992.entries[idx n]?.getD (0, 0)).1| +
          (Cache20992.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm201

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm201_c : tableEnergyNumerator t wMm201 4 1 = (862662464294692446564098411909788991875514061398791428219290409786997750112959828859612008333558 : ℤ) := by
  exact KsIndex.NegSignProdFastMm201.eMm201_c_fast
theorem eMm201_r : tableEnergyRadius t wMm201 4 1 = (2721569020001682341459494172044225401804364854616512751464856937754447986447666916819041 : ℤ) := by
  exact KsIndex.NegSignProdFastMm201.eMm201_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm201_c
#print axioms KsIndex.NegSignProd.eMm201_r
