module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache13568
public import KsIndexLean.AlphaLowSampleCache13824

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm87 : Finset ℤ := Finset.Ioc (-2625) (-2561)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm87
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm87)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-2561) then Cache13568.entries[(n - (-2817)).toNat]?.getD (0, 0)
  else Cache13824.entries[(n - (-2561)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm87) : (-2625) < n ∧ n ≤ (-2561) := by
  simpa only [wMm87, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm87) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm87) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm87) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-2561)
  · have hi : (n - (-2817)).toNat < 256 := by omega
    have hm : 2 * Cache13568.mode (n - (-2817)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache13568.mode]
      omega
    have hc := Cache13568.checked ⟨(n - (-2817)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-2561)).toNat < 256 := by omega
    have hm : 2 * Cache13824.mode (n - (-2561)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache13824.mode]
      omega
    have hc := Cache13824.checked ⟨(n - (-2561)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm87) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm87) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm87_c_fast : tableEnergyNumerator t wMm87 4 1 = (196760429252888941276042822308845746079748882064820148604278938798689308909074942375202017363398 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm87 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm87 4 1 =
      ∑ n ∈ wMm87, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm87_r_fast : tableEnergyRadius t wMm87 4 1 = (2411770203155646811575524333524047862692288750247622023216684871296479514642201557735576 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm87 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm87 4 1 =
      ∑ n ∈ wMm87, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm87

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm87_c : tableEnergyNumerator t wMm87 4 1 = (196760429252888941276042822308845746079748882064820148604278938798689308909074942375202017363398 : ℤ) := by
  exact KsIndex.NegSignProdFastMm87.eMm87_c_fast
theorem eMm87_r : tableEnergyRadius t wMm87 4 1 = (2411770203155646811575524333524047862692288750247622023216684871296479514642201557735576 : ℤ) := by
  exact KsIndex.NegSignProdFastMm87.eMm87_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm87_c
#print axioms KsIndex.NegSignProd.eMm87_r
