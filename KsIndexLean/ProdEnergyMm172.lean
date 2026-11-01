module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache19200

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm172 : Finset ℤ := Finset.Ioc (2815) (2879)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm172

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm172)

def idx (n : ℤ) : ℕ := (n - (2815)).toNat

lemma mem_wMm172 {n : ℤ} (hn : n ∈ wMm172) : (2815) < n ∧ n ≤ (2879) := by
  simpa only [wMm172, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm172) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm172 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm172) :
    2 * Cache19200.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm172 hn
  simp only [idx, Cache19200.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm172) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm172 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm172) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm172 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm172) :
    sampleNumerator (2 * n + 1) =
      (Cache19200.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache19200.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm172) :
    sampleRadius (2 * n + 1) =
      (Cache19200.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache19200.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm172_c_fast : tableEnergyNumerator t wMm172 4 1 = (2307931022493171082870494285462008960066570913805689920165539889034522543400767338204652779757812 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm172 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm172 4 1 =
      ∑ n ∈ wMm172, ((6 * n + 4) ^ 2 - 4) *
        ((Cache19200.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm172_r_fast : tableEnergyRadius t wMm172 4 1 = (7491002001032925568516043977160931526218440402432862674030277561813112311886040836935894 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm172 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm172 4 1 =
      ∑ n ∈ wMm172, (|((6 * n + 4) ^ 2 - 4)| * (Cache19200.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache19200.entries[idx n]?.getD (0, 0)).1| +
          (Cache19200.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm172

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm172_c : tableEnergyNumerator t wMm172 4 1 = (2307931022493171082870494285462008960066570913805689920165539889034522543400767338204652779757812 : ℤ) := by
  exact KsIndex.NegSignProdFastMm172.eMm172_c_fast
theorem eMm172_r : tableEnergyRadius t wMm172 4 1 = (7491002001032925568516043977160931526218440402432862674030277561813112311886040836935894 : ℤ) := by
  exact KsIndex.NegSignProdFastMm172.eMm172_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm172_c
#print axioms KsIndex.NegSignProd.eMm172_r
