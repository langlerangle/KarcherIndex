module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache23552

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm242 : Finset ℤ := Finset.Ioc (7295) (7359)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm242

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm242)

def idx (n : ℤ) : ℕ := (n - (7167)).toNat

lemma mem_wMm242 {n : ℤ} (hn : n ∈ wMm242) : (7295) < n ∧ n ≤ (7359) := by
  simpa only [wMm242, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm242) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm242 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm242) :
    2 * Cache23552.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm242 hn
  simp only [idx, Cache23552.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm242) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm242 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm242) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm242 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm242) :
    sampleNumerator (2 * n + 1) =
      (Cache23552.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache23552.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm242) :
    sampleRadius (2 * n + 1) =
      (Cache23552.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache23552.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm242_c_fast : tableEnergyNumerator t wMm242 4 1 = (362289698447897751885630714522598299316502434795088687435071096228730869893554341721657257452097 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm242 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm242 4 1 =
      ∑ n ∈ wMm242, ((6 * n + 4) ^ 2 - 4) *
        ((Cache23552.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm242_r_fast : tableEnergyRadius t wMm242 4 1 = (1114446148656558498639051452939316704570645036260476887651019766258810873639064067673181 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm242 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm242 4 1 =
      ∑ n ∈ wMm242, (|((6 * n + 4) ^ 2 - 4)| * (Cache23552.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache23552.entries[idx n]?.getD (0, 0)).1| +
          (Cache23552.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm242

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm242_c : tableEnergyNumerator t wMm242 4 1 = (362289698447897751885630714522598299316502434795088687435071096228730869893554341721657257452097 : ℤ) := by
  exact KsIndex.NegSignProdFastMm242.eMm242_c_fast
theorem eMm242_r : tableEnergyRadius t wMm242 4 1 = (1114446148656558498639051452939316704570645036260476887651019766258810873639064067673181 : ℤ) := by
  exact KsIndex.NegSignProdFastMm242.eMm242_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm242_c
#print axioms KsIndex.NegSignProd.eMm242_r
