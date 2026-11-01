module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache10496

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm37 : Finset ℤ := Finset.Ioc (-5825) (-5761)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm37

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm37)

def idx (n : ℤ) : ℕ := (n - (-5889)).toNat

lemma mem_wMm37 {n : ℤ} (hn : n ∈ wMm37) : (-5825) < n ∧ n ≤ (-5761) := by
  simpa only [wMm37, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm37) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm37 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm37) :
    2 * Cache10496.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm37 hn
  simp only [idx, Cache10496.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm37) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm37 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm37) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm37 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm37) :
    sampleNumerator (2 * n + 1) =
      (Cache10496.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache10496.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm37) :
    sampleRadius (2 * n + 1) =
      (Cache10496.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache10496.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm37_c_fast : tableEnergyNumerator t wMm37 4 1 = (57300508356447995949496840337696928481038745866595501383850645079385714709043605625231374163299 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm37 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm37 4 1 =
      ∑ n ∈ wMm37, ((6 * n + 4) ^ 2 - 4) *
        ((Cache10496.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm37_r_fast : tableEnergyRadius t wMm37 4 1 = (565396672140001609125173447283992714030187450840836277532874872217980687145590296556269 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm37 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm37 4 1 =
      ∑ n ∈ wMm37, (|((6 * n + 4) ^ 2 - 4)| * (Cache10496.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache10496.entries[idx n]?.getD (0, 0)).1| +
          (Cache10496.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm37

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm37_c : tableEnergyNumerator t wMm37 4 1 = (57300508356447995949496840337696928481038745866595501383850645079385714709043605625231374163299 : ℤ) := by
  exact KsIndex.NegSignProdFastMm37.eMm37_c_fast
theorem eMm37_r : tableEnergyRadius t wMm37 4 1 = (565396672140001609125173447283992714030187450840836277532874872217980687145590296556269 : ℤ) := by
  exact KsIndex.NegSignProdFastMm37.eMm37_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm37_c
#print axioms KsIndex.NegSignProd.eMm37_r
