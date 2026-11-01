module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache15616

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm118 : Finset ℤ := Finset.Ioc (-641) (-577)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm118

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm118)

def idx (n : ℤ) : ℕ := (n - (-769)).toNat

lemma mem_wMm118 {n : ℤ} (hn : n ∈ wMm118) : (-641) < n ∧ n ≤ (-577) := by
  simpa only [wMm118, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm118) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm118 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm118) :
    2 * Cache15616.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm118 hn
  simp only [idx, Cache15616.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm118) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm118 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm118) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm118 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm118) :
    sampleNumerator (2 * n + 1) =
      (Cache15616.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache15616.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm118) :
    sampleRadius (2 * n + 1) =
      (Cache15616.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache15616.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm118_c_fast : tableEnergyNumerator t wMm118 4 1 = (1446811754274200933645867899822155686827469116966711649907263966395949578405395282757096810517427 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm118 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm118 4 1 =
      ∑ n ∈ wMm118, ((6 * n + 4) ^ 2 - 4) *
        ((Cache15616.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm118_r_fast : tableEnergyRadius t wMm118 4 1 = (29596434044592775497129959036004378264984938764003002602779216562472356892194998014040854 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm118 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm118 4 1 =
      ∑ n ∈ wMm118, (|((6 * n + 4) ^ 2 - 4)| * (Cache15616.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache15616.entries[idx n]?.getD (0, 0)).1| +
          (Cache15616.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm118

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm118_c : tableEnergyNumerator t wMm118 4 1 = (1446811754274200933645867899822155686827469116966711649907263966395949578405395282757096810517427 : ℤ) := by
  exact KsIndex.NegSignProdFastMm118.eMm118_c_fast
theorem eMm118_r : tableEnergyRadius t wMm118 4 1 = (29596434044592775497129959036004378264984938764003002602779216562472356892194998014040854 : ℤ) := by
  exact KsIndex.NegSignProdFastMm118.eMm118_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm118_c
#print axioms KsIndex.NegSignProd.eMm118_r
