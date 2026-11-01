module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache19456
public import KsIndexLean.AlphaLowSampleCache19712

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm179 : Finset ℤ := Finset.Ioc (3263) (3327)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm179
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm179)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (3327) then Cache19456.entries[(n - (3071)).toNat]?.getD (0, 0)
  else Cache19712.entries[(n - (3327)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm179) : (3263) < n ∧ n ≤ (3327) := by
  simpa only [wMm179, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm179) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm179) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm179) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (3327)
  · have hi : (n - (3071)).toNat < 256 := by omega
    have hm : 2 * Cache19456.mode (n - (3071)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache19456.mode]
      omega
    have hc := Cache19456.checked ⟨(n - (3071)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (3327)).toNat < 256 := by omega
    have hm : 2 * Cache19712.mode (n - (3327)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache19712.mode]
      omega
    have hc := Cache19712.checked ⟨(n - (3327)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm179) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm179) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm179_c_fast : tableEnergyNumerator t wMm179 4 1 = (1732598516253382228735857157862964328262285255926425905656074227443176499918908607956930922244558 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm179 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm179 4 1 =
      ∑ n ∈ wMm179, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm179_r_fast : tableEnergyRadius t wMm179 4 1 = (5577416074898164451067118400787946959870016830451612039021007145875768190212711456513118 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm179 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm179 4 1 =
      ∑ n ∈ wMm179, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm179

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm179_c : tableEnergyNumerator t wMm179 4 1 = (1732598516253382228735857157862964328262285255926425905656074227443176499918908607956930922244558 : ℤ) := by
  exact KsIndex.NegSignProdFastMm179.eMm179_c_fast
theorem eMm179_r : tableEnergyRadius t wMm179 4 1 = (5577416074898164451067118400787946959870016830451612039021007145875768190212711456513118 : ℤ) := by
  exact KsIndex.NegSignProdFastMm179.eMm179_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm179_c
#print axioms KsIndex.NegSignProd.eMm179_r
