module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache20992
public import KsIndexLean.AlphaLowSampleCache21248

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm203 : Finset ℤ := Finset.Ioc (4799) (4863)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm203
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm203)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (4863) then Cache20992.entries[(n - (4607)).toNat]?.getD (0, 0)
  else Cache21248.entries[(n - (4863)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm203) : (4799) < n ∧ n ≤ (4863) := by
  simpa only [wMm203, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm203) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm203) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm203) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (4863)
  · have hi : (n - (4607)).toNat < 256 := by omega
    have hm : 2 * Cache20992.mode (n - (4607)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache20992.mode]
      omega
    have hc := Cache20992.checked ⟨(n - (4607)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (4863)).toNat < 256 := by omega
    have hm : 2 * Cache21248.mode (n - (4863)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache21248.mode]
      omega
    have hc := Cache21248.checked ⟨(n - (4863)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm203) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm203) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm203_c_fast : tableEnergyNumerator t wMm203 4 1 = (818467099425332950356187414576018992369386087582807433887505641027443821846237868413150643862503 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm203 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm203 4 1 =
      ∑ n ∈ wMm203, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm203_r_fast : tableEnergyRadius t wMm203 4 1 = (2578201407615024205824531048261941334467148983984794994581785368511580491709340777427732 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm203 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm203 4 1 =
      ∑ n ∈ wMm203, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm203

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm203_c : tableEnergyNumerator t wMm203 4 1 = (818467099425332950356187414576018992369386087582807433887505641027443821846237868413150643862503 : ℤ) := by
  exact KsIndex.NegSignProdFastMm203.eMm203_c_fast
theorem eMm203_r : tableEnergyRadius t wMm203 4 1 = (2578201407615024205824531048261941334467148983984794994581785368511580491709340777427732 : ℤ) := by
  exact KsIndex.NegSignProdFastMm203.eMm203_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm203_c
#print axioms KsIndex.NegSignProd.eMm203_r
