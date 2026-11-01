module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache13056

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm77 : Finset ℤ := Finset.Ioc (-3265) (-3201)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm77

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm77)

def idx (n : ℤ) : ℕ := (n - (-3329)).toNat

lemma mem_wMm77 {n : ℤ} (hn : n ∈ wMm77) : (-3265) < n ∧ n ≤ (-3201) := by
  simpa only [wMm77, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm77) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm77 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm77) :
    2 * Cache13056.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm77 hn
  simp only [idx, Cache13056.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm77) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm77 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm77) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm77 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm77) :
    sampleNumerator (2 * n + 1) =
      (Cache13056.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache13056.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm77) :
    sampleRadius (2 * n + 1) =
      (Cache13056.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache13056.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm77_c_fast : tableEnergyNumerator t wMm77 4 1 = (141169436095238986816765874327147402121675905129012024449562399622424368088656877931514047997149 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm77 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm77 4 1 =
      ∑ n ∈ wMm77, ((6 * n + 4) ^ 2 - 4) *
        ((Cache13056.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm77_r_fast : tableEnergyRadius t wMm77 4 1 = (1624677819583260553034682749790128048790875426063311607449716083762324554983506817200660 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm77 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm77 4 1 =
      ∑ n ∈ wMm77, (|((6 * n + 4) ^ 2 - 4)| * (Cache13056.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache13056.entries[idx n]?.getD (0, 0)).1| +
          (Cache13056.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm77

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm77_c : tableEnergyNumerator t wMm77 4 1 = (141169436095238986816765874327147402121675905129012024449562399622424368088656877931514047997149 : ℤ) := by
  exact KsIndex.NegSignProdFastMm77.eMm77_c_fast
theorem eMm77_r : tableEnergyRadius t wMm77 4 1 = (1624677819583260553034682749790128048790875426063311607449716083762324554983506817200660 : ℤ) := by
  exact KsIndex.NegSignProdFastMm77.eMm77_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm77_c
#print axioms KsIndex.NegSignProd.eMm77_r
