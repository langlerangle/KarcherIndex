module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache8192

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm1 : Finset ℤ := Finset.Ioc (-8129) (-8065)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm1

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm1)

def idx (n : ℤ) : ℕ := (n - (-8193)).toNat

lemma mem_wMm1 {n : ℤ} (hn : n ∈ wMm1) : (-8129) < n ∧ n ≤ (-8065) := by
  simpa only [wMm1, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm1) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm1 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm1) :
    2 * Cache8192.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm1 hn
  simp only [idx, Cache8192.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm1) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm1 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm1) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm1 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm1) :
    sampleNumerator (2 * n + 1) =
      (Cache8192.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache8192.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm1) :
    sampleRadius (2 * n + 1) =
      (Cache8192.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache8192.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm1_c_fast : tableEnergyNumerator t wMm1 4 1 = (33700086406166407668973584038713918651963975400595958829178165232378395754615523434141461217528 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm1 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm1 4 1 =
      ∑ n ∈ wMm1, ((6 * n + 4) ^ 2 - 4) *
        ((Cache8192.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm1_r_fast : tableEnergyRadius t wMm1 4 1 = (306586129352622719235378662689409746127683074034171263910661980764387844319484760629886 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm1 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm1 4 1 =
      ∑ n ∈ wMm1, (|((6 * n + 4) ^ 2 - 4)| * (Cache8192.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache8192.entries[idx n]?.getD (0, 0)).1| +
          (Cache8192.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm1

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm1_c : tableEnergyNumerator t wMm1 4 1 = (33700086406166407668973584038713918651963975400595958829178165232378395754615523434141461217528 : ℤ) := by
  exact KsIndex.NegSignProdFastMm1.eMm1_c_fast
theorem eMm1_r : tableEnergyRadius t wMm1 4 1 = (306586129352622719235378662689409746127683074034171263910661980764387844319484760629886 : ℤ) := by
  exact KsIndex.NegSignProdFastMm1.eMm1_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm1_c
#print axioms KsIndex.NegSignProd.eMm1_r
