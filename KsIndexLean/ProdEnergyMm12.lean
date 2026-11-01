module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache8960

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm12 : Finset ℤ := Finset.Ioc (-7425) (-7361)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm12

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm12)

def idx (n : ℤ) : ℕ := (n - (-7425)).toNat

lemma mem_wMm12 {n : ℤ} (hn : n ∈ wMm12) : (-7425) < n ∧ n ≤ (-7361) := by
  simpa only [wMm12, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm12) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm12 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm12) :
    2 * Cache8960.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm12 hn
  simp only [idx, Cache8960.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm12) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm12 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm12) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm12 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm12) :
    sampleNumerator (2 * n + 1) =
      (Cache8960.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache8960.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm12) :
    sampleRadius (2 * n + 1) =
      (Cache8960.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache8960.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm12_c_fast : tableEnergyNumerator t wMm12 4 1 = (38960036729254517721426413775196635364602001767734246520013107748504466991867554256674218679139 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm12 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm12 4 1 =
      ∑ n ∈ wMm12, ((6 * n + 4) ^ 2 - 4) *
        ((Cache8960.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm12_r_fast : tableEnergyRadius t wMm12 4 1 = (362178735148926647497344478645518494446271604191561572920814518220557632110574675284111 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm12 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm12 4 1 =
      ∑ n ∈ wMm12, (|((6 * n + 4) ^ 2 - 4)| * (Cache8960.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache8960.entries[idx n]?.getD (0, 0)).1| +
          (Cache8960.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm12

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm12_c : tableEnergyNumerator t wMm12 4 1 = (38960036729254517721426413775196635364602001767734246520013107748504466991867554256674218679139 : ℤ) := by
  exact KsIndex.NegSignProdFastMm12.eMm12_c_fast
theorem eMm12_r : tableEnergyRadius t wMm12 4 1 = (362178735148926647497344478645518494446271604191561572920814518220557632110574675284111 : ℤ) := by
  exact KsIndex.NegSignProdFastMm12.eMm12_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm12_c
#print axioms KsIndex.NegSignProd.eMm12_r
