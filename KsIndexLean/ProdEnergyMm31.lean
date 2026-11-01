module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache9984
public import KsIndexLean.AlphaLowSampleCache10240

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm31 : Finset ℤ := Finset.Ioc (-6209) (-6145)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm31
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm31)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-6145) then Cache9984.entries[(n - (-6401)).toNat]?.getD (0, 0)
  else Cache10240.entries[(n - (-6145)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm31) : (-6209) < n ∧ n ≤ (-6145) := by
  simpa only [wMm31, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm31) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm31) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm31) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-6145)
  · have hi : (n - (-6401)).toNat < 256 := by omega
    have hm : 2 * Cache9984.mode (n - (-6401)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache9984.mode]
      omega
    have hc := Cache9984.checked ⟨(n - (-6401)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-6145)).toNat < 256 := by omega
    have hm : 2 * Cache10240.mode (n - (-6145)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache10240.mode]
      omega
    have hc := Cache10240.checked ⟨(n - (-6145)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm31) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm31) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm31_c_fast : tableEnergyNumerator t wMm31 4 1 = (51792246580033764351428484408861571005366007238194881553425724914671443382520885609668913009730 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm31 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm31 4 1 =
      ∑ n ∈ wMm31, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm31_r_fast : tableEnergyRadius t wMm31 4 1 = (502965586305320513184218554227173187456256614955110336478871540783949313151647258013492 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm31 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm31 4 1 =
      ∑ n ∈ wMm31, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm31

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm31_c : tableEnergyNumerator t wMm31 4 1 = (51792246580033764351428484408861571005366007238194881553425724914671443382520885609668913009730 : ℤ) := by
  exact KsIndex.NegSignProdFastMm31.eMm31_c_fast
theorem eMm31_r : tableEnergyRadius t wMm31 4 1 = (502965586305320513184218554227173187456256614955110336478871540783949313151647258013492 : ℤ) := by
  exact KsIndex.NegSignProdFastMm31.eMm31_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm31_c
#print axioms KsIndex.NegSignProd.eMm31_r
