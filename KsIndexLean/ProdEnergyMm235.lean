module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache23040
public import KsIndexLean.AlphaLowSampleCache23296

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm235 : Finset ℤ := Finset.Ioc (6847) (6911)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm235
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm235)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (6911) then Cache23040.entries[(n - (6655)).toNat]?.getD (0, 0)
  else Cache23296.entries[(n - (6911)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm235) : (6847) < n ∧ n ≤ (6911) := by
  simpa only [wMm235, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm235) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm235) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm235) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (6911)
  · have hi : (n - (6655)).toNat < 256 := by omega
    have hm : 2 * Cache23040.mode (n - (6655)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache23040.mode]
      omega
    have hc := Cache23040.checked ⟨(n - (6655)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (6911)).toNat < 256 := by omega
    have hm : 2 * Cache23296.mode (n - (6911)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache23296.mode]
      omega
    have hc := Cache23296.checked ⟨(n - (6911)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm235) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm235) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm235_c_fast : tableEnergyNumerator t wMm235 4 1 = (409857423159895585640099801986294117064638164428193261978068973476053309388967318613667007196507 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm235 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm235 4 1 =
      ∑ n ∈ wMm235, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm235_r_fast : tableEnergyRadius t wMm235 4 1 = (1265323566314045546768213118312018350689002614999741454413886614062559476940080473417817 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm235 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm235 4 1 =
      ∑ n ∈ wMm235, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm235

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm235_c : tableEnergyNumerator t wMm235 4 1 = (409857423159895585640099801986294117064638164428193261978068973476053309388967318613667007196507 : ℤ) := by
  exact KsIndex.NegSignProdFastMm235.eMm235_c_fast
theorem eMm235_r : tableEnergyRadius t wMm235 4 1 = (1265323566314045546768213118312018350689002614999741454413886614062559476940080473417817 : ℤ) := by
  exact KsIndex.NegSignProdFastMm235.eMm235_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm235_c
#print axioms KsIndex.NegSignProd.eMm235_r
