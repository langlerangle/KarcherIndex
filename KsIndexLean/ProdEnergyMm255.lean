module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache24320
public import KsIndexLean.AlphaLowSampleCache24576

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm255 : Finset ℤ := Finset.Ioc (8127) (8191)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm255
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm255)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (8191) then Cache24320.entries[(n - (7935)).toNat]?.getD (0, 0)
  else Cache24576.entries[(n - (8191)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm255) : (8127) < n ∧ n ≤ (8191) := by
  simpa only [wMm255, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm255) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm255) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm255) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (8191)
  · have hi : (n - (7935)).toNat < 256 := by omega
    have hm : 2 * Cache24320.mode (n - (7935)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache24320.mode]
      omega
    have hc := Cache24320.checked ⟨(n - (7935)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (8191)).toNat < 256 := by omega
    have hm : 2 * Cache24576.mode (n - (8191)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache24576.mode]
      omega
    have hc := Cache24576.checked ⟨(n - (8191)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm255) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm255) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm255_c_fast : tableEnergyNumerator t wMm255 4 1 = (293598725815910400888105433467197916399501076902472931101319049709454286483299570480030251470304 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm255 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm255 4 1 =
      ∑ n ∈ wMm255, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm255_r_fast : tableEnergyRadius t wMm255 4 1 = (897605569518276628918648232940506860023822573012099589566397517682473913147783882407545 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm255 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm255 4 1 =
      ∑ n ∈ wMm255, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm255

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm255_c : tableEnergyNumerator t wMm255 4 1 = (293598725815910400888105433467197916399501076902472931101319049709454286483299570480030251470304 : ℤ) := by
  exact KsIndex.NegSignProdFastMm255.eMm255_c_fast
theorem eMm255_r : tableEnergyRadius t wMm255 4 1 = (897605569518276628918648232940506860023822573012099589566397517682473913147783882407545 : ℤ) := by
  exact KsIndex.NegSignProdFastMm255.eMm255_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm255_c
#print axioms KsIndex.NegSignProd.eMm255_r
