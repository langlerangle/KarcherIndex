module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache11520
public import KsIndexLean.AlphaLowSampleCache11776

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm55 : Finset ℤ := Finset.Ioc (-4673) (-4609)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm55
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm55)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-4609) then Cache11520.entries[(n - (-4865)).toNat]?.getD (0, 0)
  else Cache11776.entries[(n - (-4609)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm55) : (-4673) < n ∧ n ≤ (-4609) := by
  simpa only [wMm55, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm55) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm55) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm55) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-4609)
  · have hi : (n - (-4865)).toNat < 256 := by omega
    have hm : 2 * Cache11520.mode (n - (-4865)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache11520.mode]
      omega
    have hc := Cache11520.checked ⟨(n - (-4865)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-4609)).toNat < 256 := by omega
    have hm : 2 * Cache11776.mode (n - (-4609)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache11776.mode]
      omega
    have hc := Cache11776.checked ⟨(n - (-4609)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm55) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm55) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm55_c_fast : tableEnergyNumerator t wMm55 4 1 = (81027522243162902327648911124662707760236611803244085623962065366764069725983372115688706985706 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm55 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm55 4 1 =
      ∑ n ∈ wMm55, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm55_r_fast : tableEnergyRadius t wMm55 4 1 = (845989489433956671883438079172704479924636115997630914461115168852011357964239508107435 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm55 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm55 4 1 =
      ∑ n ∈ wMm55, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm55

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm55_c : tableEnergyNumerator t wMm55 4 1 = (81027522243162902327648911124662707760236611803244085623962065366764069725983372115688706985706 : ℤ) := by
  exact KsIndex.NegSignProdFastMm55.eMm55_c_fast
theorem eMm55_r : tableEnergyRadius t wMm55 4 1 = (845989489433956671883438079172704479924636115997630914461115168852011357964239508107435 : ℤ) := by
  exact KsIndex.NegSignProdFastMm55.eMm55_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm55_c
#print axioms KsIndex.NegSignProd.eMm55_r
