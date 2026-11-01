module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache19200
public import KsIndexLean.AlphaLowSampleCache19456

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm175 : Finset ℤ := Finset.Ioc (3007) (3071)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm175
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm175)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (3071) then Cache19200.entries[(n - (2815)).toNat]?.getD (0, 0)
  else Cache19456.entries[(n - (3071)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm175) : (3007) < n ∧ n ≤ (3071) := by
  simpa only [wMm175, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm175) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm175) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm175) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (3071)
  · have hi : (n - (2815)).toNat < 256 := by omega
    have hm : 2 * Cache19200.mode (n - (2815)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache19200.mode]
      omega
    have hc := Cache19200.checked ⟨(n - (2815)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (3071)).toNat < 256 := by omega
    have hm : 2 * Cache19456.mode (n - (3071)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache19456.mode]
      omega
    have hc := Cache19456.checked ⟨(n - (3071)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm175) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm175) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm175_c_fast : tableEnergyNumerator t wMm175 4 1 = (2030503674805638676453402130506632971152025813632450961992164291422113541127712255712887521125115 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm175 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm175 4 1 =
      ∑ n ∈ wMm175, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm175_r_fast : tableEnergyRadius t wMm175 4 1 = (6566324685656558017018984914059549598910340254089520248080058755290360074752297387248317 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm175 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm175 4 1 =
      ∑ n ∈ wMm175, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm175

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm175_c : tableEnergyNumerator t wMm175 4 1 = (2030503674805638676453402130506632971152025813632450961992164291422113541127712255712887521125115 : ℤ) := by
  exact KsIndex.NegSignProdFastMm175.eMm175_c_fast
theorem eMm175_r : tableEnergyRadius t wMm175 4 1 = (6566324685656558017018984914059549598910340254089520248080058755290360074752297387248317 : ℤ) := by
  exact KsIndex.NegSignProdFastMm175.eMm175_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm175_c
#print axioms KsIndex.NegSignProd.eMm175_r
