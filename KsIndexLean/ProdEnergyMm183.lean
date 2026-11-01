module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache19712
public import KsIndexLean.AlphaLowSampleCache19968

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm183 : Finset ℤ := Finset.Ioc (3519) (3583)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm183
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm183)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (3583) then Cache19712.entries[(n - (3327)).toNat]?.getD (0, 0)
  else Cache19968.entries[(n - (3583)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm183) : (3519) < n ∧ n ≤ (3583) := by
  simpa only [wMm183, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm183) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm183) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm183) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (3583)
  · have hi : (n - (3327)).toNat < 256 := by omega
    have hm : 2 * Cache19712.mode (n - (3327)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache19712.mode]
      omega
    have hc := Cache19712.checked ⟨(n - (3327)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (3583)).toNat < 256 := by omega
    have hm : 2 * Cache19968.mode (n - (3583)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache19968.mode]
      omega
    have hc := Cache19968.checked ⟨(n - (3583)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm183) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm183) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm183_c_fast : tableEnergyNumerator t wMm183 4 1 = (1496135268521298280109307634637033003806891851335562895944763877885568500338897539658437379418171 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm183 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm183 4 1 =
      ∑ n ∈ wMm183, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm183_r_fast : tableEnergyRadius t wMm183 4 1 = (4795883039759343009712120652439633648313062468888364064507312138686426077708852881429838 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm183 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm183 4 1 =
      ∑ n ∈ wMm183, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm183

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm183_c : tableEnergyNumerator t wMm183 4 1 = (1496135268521298280109307634637033003806891851335562895944763877885568500338897539658437379418171 : ℤ) := by
  exact KsIndex.NegSignProdFastMm183.eMm183_c_fast
theorem eMm183_r : tableEnergyRadius t wMm183 4 1 = (4795883039759343009712120652439633648313062468888364064507312138686426077708852881429838 : ℤ) := by
  exact KsIndex.NegSignProdFastMm183.eMm183_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm183_c
#print axioms KsIndex.NegSignProd.eMm183_r
