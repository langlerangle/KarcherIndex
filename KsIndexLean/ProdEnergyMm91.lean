module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache13824
public import KsIndexLean.AlphaLowSampleCache14080

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm91 : Finset ℤ := Finset.Ioc (-2369) (-2305)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm91
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm91)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-2305) then Cache13824.entries[(n - (-2561)).toNat]?.getD (0, 0)
  else Cache14080.entries[(n - (-2305)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm91) : (-2369) < n ∧ n ≤ (-2305) := by
  simpa only [wMm91, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm91) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm91) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm91) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-2305)
  · have hi : (n - (-2561)).toNat < 256 := by omega
    have hm : 2 * Cache13824.mode (n - (-2561)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache13824.mode]
      omega
    have hc := Cache13824.checked ⟨(n - (-2561)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-2305)).toNat < 256 := by omega
    have hm : 2 * Cache14080.mode (n - (-2305)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache14080.mode]
      omega
    have hc := Cache14080.checked ⟨(n - (-2305)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm91) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm91) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm91_c_fast : tableEnergyNumerator t wMm91 4 1 = (229629709173112408212617440783503093859233769697767650604827481065416954617834948957634758448708 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm91 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm91 4 1 =
      ∑ n ∈ wMm91, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm91_r_fast : tableEnergyRadius t wMm91 4 1 = (2902555215988186610090672733509321956941925416744204126081571055501640653694814929041650 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm91 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm91 4 1 =
      ∑ n ∈ wMm91, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm91

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm91_c : tableEnergyNumerator t wMm91 4 1 = (229629709173112408212617440783503093859233769697767650604827481065416954617834948957634758448708 : ℤ) := by
  exact KsIndex.NegSignProdFastMm91.eMm91_c_fast
theorem eMm91_r : tableEnergyRadius t wMm91 4 1 = (2902555215988186610090672733509321956941925416744204126081571055501640653694814929041650 : ℤ) := by
  exact KsIndex.NegSignProdFastMm91.eMm91_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm91_c
#print axioms KsIndex.NegSignProd.eMm91_r
