module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache12032

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm61 : Finset ℤ := Finset.Ioc (-4289) (-4225)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm61

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm61)

def idx (n : ℤ) : ℕ := (n - (-4353)).toNat

lemma mem_wMm61 {n : ℤ} (hn : n ∈ wMm61) : (-4289) < n ∧ n ≤ (-4225) := by
  simpa only [wMm61, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm61) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm61 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm61) :
    2 * Cache12032.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm61 hn
  simp only [idx, Cache12032.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm61) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm61 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm61) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm61 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm61) :
    sampleNumerator (2 * n + 1) =
      (Cache12032.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache12032.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm61) :
    sampleRadius (2 * n + 1) =
      (Cache12032.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache12032.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm61_c_fast : tableEnergyNumerator t wMm61 4 1 = (92625898268700008688790820709122262086922939100331208246584377561388677599725067620869194274275 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm61 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm61 4 1 =
      ∑ n ∈ wMm61, ((6 * n + 4) ^ 2 - 4) *
        ((Cache12032.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm61_r_fast : tableEnergyRadius t wMm61 4 1 = (989236132153974885347082414557566095472521013295423801767639764477883253299173788397501 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm61 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm61 4 1 =
      ∑ n ∈ wMm61, (|((6 * n + 4) ^ 2 - 4)| * (Cache12032.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache12032.entries[idx n]?.getD (0, 0)).1| +
          (Cache12032.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm61

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm61_c : tableEnergyNumerator t wMm61 4 1 = (92625898268700008688790820709122262086922939100331208246584377561388677599725067620869194274275 : ℤ) := by
  exact KsIndex.NegSignProdFastMm61.eMm61_c_fast
theorem eMm61_r : tableEnergyRadius t wMm61 4 1 = (989236132153974885347082414557566095472521013295423801767639764477883253299173788397501 : ℤ) := by
  exact KsIndex.NegSignProdFastMm61.eMm61_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm61_c
#print axioms KsIndex.NegSignProd.eMm61_r
