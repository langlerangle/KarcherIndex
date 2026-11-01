module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache10496

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm36 : Finset ℤ := Finset.Ioc (-5889) (-5825)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm36

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm36)

def idx (n : ℤ) : ℕ := (n - (-5889)).toNat

lemma mem_wMm36 {n : ℤ} (hn : n ∈ wMm36) : (-5889) < n ∧ n ≤ (-5825) := by
  simpa only [wMm36, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm36) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm36 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm36) :
    2 * Cache10496.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm36 hn
  simp only [idx, Cache10496.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm36) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm36 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm36) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm36 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm36) :
    sampleNumerator (2 * n + 1) =
      (Cache10496.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache10496.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm36) :
    sampleRadius (2 * n + 1) =
      (Cache10496.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache10496.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm36_c_fast : tableEnergyNumerator t wMm36 4 1 = (56318974832779770125122070684969529142465717777698304235569580615089799811892797782960619770763 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm36 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm36 4 1 =
      ∑ n ∈ wMm36, ((6 * n + 4) ^ 2 - 4) *
        ((Cache10496.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm36_r_fast : tableEnergyRadius t wMm36 4 1 = (554190489903529463986904258345557794323965408643170521866946691114541696984225502148384 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm36 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm36 4 1 =
      ∑ n ∈ wMm36, (|((6 * n + 4) ^ 2 - 4)| * (Cache10496.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache10496.entries[idx n]?.getD (0, 0)).1| +
          (Cache10496.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm36

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm36_c : tableEnergyNumerator t wMm36 4 1 = (56318974832779770125122070684969529142465717777698304235569580615089799811892797782960619770763 : ℤ) := by
  exact KsIndex.NegSignProdFastMm36.eMm36_c_fast
theorem eMm36_r : tableEnergyRadius t wMm36 4 1 = (554190489903529463986904258345557794323965408643170521866946691114541696984225502148384 : ℤ) := by
  exact KsIndex.NegSignProdFastMm36.eMm36_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm36_c
#print axioms KsIndex.NegSignProd.eMm36_r
