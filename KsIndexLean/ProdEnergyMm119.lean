module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache15616
public import KsIndexLean.AlphaLowSampleCache15872

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm119 : Finset ℤ := Finset.Ioc (-577) (-513)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm119
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm119)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-513) then Cache15616.entries[(n - (-769)).toNat]?.getD (0, 0)
  else Cache15872.entries[(n - (-513)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm119) : (-577) < n ∧ n ≤ (-513) := by
  simpa only [wMm119, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm119) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm119) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm119) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-513)
  · have hi : (n - (-769)).toNat < 256 := by omega
    have hm : 2 * Cache15616.mode (n - (-769)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache15616.mode]
      omega
    have hc := Cache15616.checked ⟨(n - (-769)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-513)).toNat < 256 := by omega
    have hm : 2 * Cache15872.mode (n - (-513)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache15872.mode]
      omega
    have hc := Cache15872.checked ⟨(n - (-513)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm119) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm119) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm119_c_fast : tableEnergyNumerator t wMm119 4 1 = (1653884634779816717922825490090439003194666180802059141384071020273290277011156657710753787783307 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm119 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm119 4 1 =
      ∑ n ∈ wMm119, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm119_r_fast : tableEnergyRadius t wMm119 4 1 = (35545928583798183599001657286546155352018598207906432029066907577643866787404824675649098 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm119 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm119 4 1 =
      ∑ n ∈ wMm119, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm119

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm119_c : tableEnergyNumerator t wMm119 4 1 = (1653884634779816717922825490090439003194666180802059141384071020273290277011156657710753787783307 : ℤ) := by
  exact KsIndex.NegSignProdFastMm119.eMm119_c_fast
theorem eMm119_r : tableEnergyRadius t wMm119 4 1 = (35545928583798183599001657286546155352018598207906432029066907577643866787404824675649098 : ℤ) := by
  exact KsIndex.NegSignProdFastMm119.eMm119_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm119_c
#print axioms KsIndex.NegSignProd.eMm119_r
