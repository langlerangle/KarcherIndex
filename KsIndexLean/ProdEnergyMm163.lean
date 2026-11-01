module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache18432
public import KsIndexLean.AlphaLowSampleCache18688

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm163 : Finset ℤ := Finset.Ioc (2239) (2303)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm163
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm163)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (2303) then Cache18432.entries[(n - (2047)).toNat]?.getD (0, 0)
  else Cache18688.entries[(n - (2303)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm163) : (2239) < n ∧ n ≤ (2303) := by
  simpa only [wMm163, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm163) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm163) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm163) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (2303)
  · have hi : (n - (2047)).toNat < 256 := by omega
    have hm : 2 * Cache18432.mode (n - (2047)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache18432.mode]
      omega
    have hc := Cache18432.checked ⟨(n - (2047)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (2303)).toNat < 256 := by omega
    have hm : 2 * Cache18688.mode (n - (2303)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache18688.mode]
      omega
    have hc := Cache18688.checked ⟨(n - (2303)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm163) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm163) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm163_c_fast : tableEnergyNumerator t wMm163 4 1 = (3597352115114906118112555867025756495105979719408609269904260687206645787610570037708462589159604 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm163 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm163 4 1 =
      ∑ n ∈ wMm163, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm163_r_fast : tableEnergyRadius t wMm163 4 1 = (11825577818997112081616461244827176984299711751010820218092760351797626242362581432827959 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm163 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm163 4 1 =
      ∑ n ∈ wMm163, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm163

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm163_c : tableEnergyNumerator t wMm163 4 1 = (3597352115114906118112555867025756495105979719408609269904260687206645787610570037708462589159604 : ℤ) := by
  exact KsIndex.NegSignProdFastMm163.eMm163_c_fast
theorem eMm163_r : tableEnergyRadius t wMm163 4 1 = (11825577818997112081616461244827176984299711751010820218092760351797626242362581432827959 : ℤ) := by
  exact KsIndex.NegSignProdFastMm163.eMm163_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm163_c
#print axioms KsIndex.NegSignProd.eMm163_r
