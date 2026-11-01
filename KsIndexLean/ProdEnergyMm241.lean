module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache23552

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm241 : Finset ℤ := Finset.Ioc (7231) (7295)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm241

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm241)

def idx (n : ℤ) : ℕ := (n - (7167)).toNat

lemma mem_wMm241 {n : ℤ} (hn : n ∈ wMm241) : (7231) < n ∧ n ≤ (7295) := by
  simpa only [wMm241, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm241) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm241 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm241) :
    2 * Cache23552.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm241 hn
  simp only [idx, Cache23552.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm241) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm241 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm241) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm241 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm241) :
    sampleNumerator (2 * n + 1) =
      (Cache23552.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache23552.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm241) :
    sampleRadius (2 * n + 1) =
      (Cache23552.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache23552.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm241_c_fast : tableEnergyNumerator t wMm241 4 1 = (368557396086949649477428051871895791999436812338199821309478633543909800976819744329365084271363 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm241 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm241 4 1 =
      ∑ n ∈ wMm241, ((6 * n + 4) ^ 2 - 4) *
        ((Cache23552.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm241_r_fast : tableEnergyRadius t wMm241 4 1 = (1134294996852051953294971860124940764027172101847876588330383682215489027059459516084504 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm241 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm241 4 1 =
      ∑ n ∈ wMm241, (|((6 * n + 4) ^ 2 - 4)| * (Cache23552.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache23552.entries[idx n]?.getD (0, 0)).1| +
          (Cache23552.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm241

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm241_c : tableEnergyNumerator t wMm241 4 1 = (368557396086949649477428051871895791999436812338199821309478633543909800976819744329365084271363 : ℤ) := by
  exact KsIndex.NegSignProdFastMm241.eMm241_c_fast
theorem eMm241_r : tableEnergyRadius t wMm241 4 1 = (1134294996852051953294971860124940764027172101847876588330383682215489027059459516084504 : ℤ) := by
  exact KsIndex.NegSignProdFastMm241.eMm241_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm241_c
#print axioms KsIndex.NegSignProd.eMm241_r
