module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache19968

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm185 : Finset ℤ := Finset.Ioc (3647) (3711)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm185

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm185)

def idx (n : ℤ) : ℕ := (n - (3583)).toNat

lemma mem_wMm185 {n : ℤ} (hn : n ∈ wMm185) : (3647) < n ∧ n ≤ (3711) := by
  simpa only [wMm185, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm185) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm185 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm185) :
    2 * Cache19968.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm185 hn
  simp only [idx, Cache19968.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm185) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm185 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm185) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm185 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm185) :
    sampleNumerator (2 * n + 1) =
      (Cache19968.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache19968.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm185) :
    sampleRadius (2 * n + 1) =
      (Cache19968.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache19968.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm185_c_fast : tableEnergyNumerator t wMm185 4 1 = (1395781378996691768047572584933440574189960295025626311096459620061259903665680410754385363554784 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm185 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm185 4 1 =
      ∑ n ∈ wMm185, ((6 * n + 4) ^ 2 - 4) *
        ((Cache19968.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm185_r_fast : tableEnergyRadius t wMm185 4 1 = (4465239428433694632793950045731168495154180875033593556180377890101753431399744892697928 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm185 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm185 4 1 =
      ∑ n ∈ wMm185, (|((6 * n + 4) ^ 2 - 4)| * (Cache19968.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache19968.entries[idx n]?.getD (0, 0)).1| +
          (Cache19968.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm185

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm185_c : tableEnergyNumerator t wMm185 4 1 = (1395781378996691768047572584933440574189960295025626311096459620061259903665680410754385363554784 : ℤ) := by
  exact KsIndex.NegSignProdFastMm185.eMm185_c_fast
theorem eMm185_r : tableEnergyRadius t wMm185 4 1 = (4465239428433694632793950045731168495154180875033593556180377890101753431399744892697928 : ℤ) := by
  exact KsIndex.NegSignProdFastMm185.eMm185_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm185_c
#print axioms KsIndex.NegSignProd.eMm185_r
