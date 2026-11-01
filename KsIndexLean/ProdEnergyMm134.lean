module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache16640

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm134 : Finset ℤ := Finset.Ioc (383) (447)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm134

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm134)

def idx (n : ℤ) : ℕ := (n - (255)).toNat

lemma mem_wMm134 {n : ℤ} (hn : n ∈ wMm134) : (383) < n ∧ n ≤ (447) := by
  simpa only [wMm134, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm134) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm134 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm134) :
    2 * Cache16640.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm134 hn
  simp only [idx, Cache16640.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm134) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm134 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm134) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm134 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm134) :
    sampleNumerator (2 * n + 1) =
      (Cache16640.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache16640.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm134) :
    sampleRadius (2 * n + 1) =
      (Cache16640.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache16640.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm134_c_fast : tableEnergyNumerator t wMm134 4 1 = (102903611245657096987874542011770853153451076335378124144973260755498730150627882346892760324098511 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm134 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm134 4 1 =
      ∑ n ∈ wMm134, ((6 * n + 4) ^ 2 - 4) *
        ((Cache16640.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm134_r_fast : tableEnergyRadius t wMm134 4 1 = (371590013843749068682377769378508675604948680067304996454244459389626991400733392197258536 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm134 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm134 4 1 =
      ∑ n ∈ wMm134, (|((6 * n + 4) ^ 2 - 4)| * (Cache16640.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache16640.entries[idx n]?.getD (0, 0)).1| +
          (Cache16640.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm134

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm134_c : tableEnergyNumerator t wMm134 4 1 = (102903611245657096987874542011770853153451076335378124144973260755498730150627882346892760324098511 : ℤ) := by
  exact KsIndex.NegSignProdFastMm134.eMm134_c_fast
theorem eMm134_r : tableEnergyRadius t wMm134 4 1 = (371590013843749068682377769378508675604948680067304996454244459389626991400733392197258536 : ℤ) := by
  exact KsIndex.NegSignProdFastMm134.eMm134_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm134_c
#print axioms KsIndex.NegSignProd.eMm134_r
