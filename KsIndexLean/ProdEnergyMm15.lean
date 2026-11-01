module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache8960
public import KsIndexLean.AlphaLowSampleCache9216

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm15 : Finset ℤ := Finset.Ioc (-7233) (-7169)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm15
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm15)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-7169) then Cache8960.entries[(n - (-7425)).toNat]?.getD (0, 0)
  else Cache9216.entries[(n - (-7169)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm15) : (-7233) < n ∧ n ≤ (-7169) := by
  simpa only [wMm15, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm15) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm15) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm15) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-7169)
  · have hi : (n - (-7425)).toNat < 256 := by omega
    have hm : 2 * Cache8960.mode (n - (-7425)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache8960.mode]
      omega
    have hc := Cache8960.checked ⟨(n - (-7425)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-7169)).toNat < 256 := by omega
    have hm : 2 * Cache9216.mode (n - (-7169)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache9216.mode]
      omega
    have hc := Cache9216.checked ⟨(n - (-7169)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm15) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm15) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm15_c_fast : tableEnergyNumerator t wMm15 4 1 = (40624853934168904452908239180996820169227849520871925919383704586616500628588166453978934663826 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm15 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm15 4 1 =
      ∑ n ∈ wMm15, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm15_r_fast : tableEnergyRadius t wMm15 4 1 = (380046368403092707885706329345077757355631478337686985080302566913511323285228607963781 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm15 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm15 4 1 =
      ∑ n ∈ wMm15, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm15

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm15_c : tableEnergyNumerator t wMm15 4 1 = (40624853934168904452908239180996820169227849520871925919383704586616500628588166453978934663826 : ℤ) := by
  exact KsIndex.NegSignProdFastMm15.eMm15_c_fast
theorem eMm15_r : tableEnergyRadius t wMm15 4 1 = (380046368403092707885706329345077757355631478337686985080302566913511323285228607963781 : ℤ) := by
  exact KsIndex.NegSignProdFastMm15.eMm15_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm15_c
#print axioms KsIndex.NegSignProd.eMm15_r
