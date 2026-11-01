module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache19712

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm181 : Finset ℤ := Finset.Ioc (3391) (3455)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm181

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm181)

def idx (n : ℤ) : ℕ := (n - (3327)).toNat

lemma mem_wMm181 {n : ℤ} (hn : n ∈ wMm181) : (3391) < n ∧ n ≤ (3455) := by
  simpa only [wMm181, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm181) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm181 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm181) :
    2 * Cache19712.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm181 hn
  simp only [idx, Cache19712.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm181) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm181 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm181) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm181 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm181) :
    sampleNumerator (2 * n + 1) =
      (Cache19712.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache19712.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm181) :
    sampleRadius (2 * n + 1) =
      (Cache19712.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache19712.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm181_c_fast : tableEnergyNumerator t wMm181 4 1 = (1607814934434970510123872905935329430155123733653392385296488730336848408149558910218986175264504 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm181 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm181 4 1 =
      ∑ n ∈ wMm181, ((6 * n + 4) ^ 2 - 4) *
        ((Cache19712.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm181_r_fast : tableEnergyRadius t wMm181 4 1 = (5164586746179472052505493137888813938827092628689707922871763825785619121820024605044300 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm181 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm181 4 1 =
      ∑ n ∈ wMm181, (|((6 * n + 4) ^ 2 - 4)| * (Cache19712.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache19712.entries[idx n]?.getD (0, 0)).1| +
          (Cache19712.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm181

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm181_c : tableEnergyNumerator t wMm181 4 1 = (1607814934434970510123872905935329430155123733653392385296488730336848408149558910218986175264504 : ℤ) := by
  exact KsIndex.NegSignProdFastMm181.eMm181_c_fast
theorem eMm181_r : tableEnergyRadius t wMm181 4 1 = (5164586746179472052505493137888813938827092628689707922871763825785619121820024605044300 : ℤ) := by
  exact KsIndex.NegSignProdFastMm181.eMm181_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm181_c
#print axioms KsIndex.NegSignProd.eMm181_r
