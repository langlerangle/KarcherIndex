module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache15104

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm109 : Finset ℤ := Finset.Ioc (-1217) (-1153)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm109

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm109)

def idx (n : ℤ) : ℕ := (n - (-1281)).toNat

lemma mem_wMm109 {n : ℤ} (hn : n ∈ wMm109) : (-1217) < n ∧ n ≤ (-1153) := by
  simpa only [wMm109, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm109) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm109 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm109) :
    2 * Cache15104.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm109 hn
  simp only [idx, Cache15104.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm109) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm109 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm109) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm109 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm109) :
    sampleNumerator (2 * n + 1) =
      (Cache15104.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache15104.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm109) :
    sampleRadius (2 * n + 1) =
      (Cache15104.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache15104.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm109_c_fast : tableEnergyNumerator t wMm109 4 1 = (606982528513167550231139381964151910794767113138566198717797610402749084085408059013281494939398 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm109 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm109 4 1 =
      ∑ n ∈ wMm109, ((6 * n + 4) ^ 2 - 4) *
        ((Cache15104.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm109_r_fast : tableEnergyRadius t wMm109 4 1 = (9566320975075128783637226803023446896079476600153617480936968033698524641549923361324241 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm109 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm109 4 1 =
      ∑ n ∈ wMm109, (|((6 * n + 4) ^ 2 - 4)| * (Cache15104.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache15104.entries[idx n]?.getD (0, 0)).1| +
          (Cache15104.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm109

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm109_c : tableEnergyNumerator t wMm109 4 1 = (606982528513167550231139381964151910794767113138566198717797610402749084085408059013281494939398 : ℤ) := by
  exact KsIndex.NegSignProdFastMm109.eMm109_c_fast
theorem eMm109_r : tableEnergyRadius t wMm109 4 1 = (9566320975075128783637226803023446896079476600153617480936968033698524641549923361324241 : ℤ) := by
  exact KsIndex.NegSignProdFastMm109.eMm109_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm109_c
#print axioms KsIndex.NegSignProd.eMm109_r
