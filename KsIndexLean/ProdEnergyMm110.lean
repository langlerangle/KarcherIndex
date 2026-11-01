module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache15104

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm110 : Finset ℤ := Finset.Ioc (-1153) (-1089)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm110

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm110)

def idx (n : ℤ) : ℕ := (n - (-1281)).toNat

lemma mem_wMm110 {n : ℤ} (hn : n ∈ wMm110) : (-1153) < n ∧ n ≤ (-1089) := by
  simpa only [wMm110, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm110) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm110 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm110) :
    2 * Cache15104.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm110 hn
  simp only [idx, Cache15104.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm110) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm110 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm110) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm110 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm110) :
    sampleNumerator (2 * n + 1) =
      (Cache15104.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache15104.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm110) :
    sampleRadius (2 * n + 1) =
      (Cache15104.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache15104.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm110_c_fast : tableEnergyNumerator t wMm110 4 1 = (654993563995379997470514990892450509445579274879560870128480701162199250951469630280609336442153 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm110 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm110 4 1 =
      ∑ n ∈ wMm110, ((6 * n + 4) ^ 2 - 4) *
        ((Cache15104.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm110_r_fast : tableEnergyRadius t wMm110 4 1 = (10529471570260203700398099218375649750598599539138770407196572321133196731857279481050519 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm110 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm110 4 1 =
      ∑ n ∈ wMm110, (|((6 * n + 4) ^ 2 - 4)| * (Cache15104.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache15104.entries[idx n]?.getD (0, 0)).1| +
          (Cache15104.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm110

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm110_c : tableEnergyNumerator t wMm110 4 1 = (654993563995379997470514990892450509445579274879560870128480701162199250951469630280609336442153 : ℤ) := by
  exact KsIndex.NegSignProdFastMm110.eMm110_c_fast
theorem eMm110_r : tableEnergyRadius t wMm110 4 1 = (10529471570260203700398099218375649750598599539138770407196572321133196731857279481050519 : ℤ) := by
  exact KsIndex.NegSignProdFastMm110.eMm110_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm110_c
#print axioms KsIndex.NegSignProd.eMm110_r
