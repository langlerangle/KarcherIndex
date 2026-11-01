module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache21760
public import KsIndexLean.AlphaLowSampleCache22016

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm215 : Finset ℤ := Finset.Ioc (5567) (5631)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm215
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm215)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (5631) then Cache21760.entries[(n - (5375)).toNat]?.getD (0, 0)
  else Cache22016.entries[(n - (5631)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm215) : (5567) < n ∧ n ≤ (5631) := by
  simpa only [wMm215, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm215) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm215) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm215) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (5631)
  · have hi : (n - (5375)).toNat < 256 := by omega
    have hm : 2 * Cache21760.mode (n - (5375)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache21760.mode]
      omega
    have hc := Cache21760.checked ⟨(n - (5375)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (5631)).toNat < 256 := by omega
    have hm : 2 * Cache22016.mode (n - (5631)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache22016.mode]
      omega
    have hc := Cache22016.checked ⟨(n - (5631)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm215) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm215) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm215_c_fast : tableEnergyNumerator t wMm215 4 1 = (613141203091533109367643235216301699961535462537165721650743776779773876123351619917157724606886 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm215 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm215 4 1 =
      ∑ n ∈ wMm215, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm215_r_fast : tableEnergyRadius t wMm215 4 1 = (1915269246185180233209949360293993503679016434389035473286589197066873545894894291687419 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm215 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm215 4 1 =
      ∑ n ∈ wMm215, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm215

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm215_c : tableEnergyNumerator t wMm215 4 1 = (613141203091533109367643235216301699961535462537165721650743776779773876123351619917157724606886 : ℤ) := by
  exact KsIndex.NegSignProdFastMm215.eMm215_c_fast
theorem eMm215_r : tableEnergyRadius t wMm215 4 1 = (1915269246185180233209949360293993503679016434389035473286589197066873545894894291687419 : ℤ) := by
  exact KsIndex.NegSignProdFastMm215.eMm215_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm215_c
#print axioms KsIndex.NegSignProd.eMm215_r
