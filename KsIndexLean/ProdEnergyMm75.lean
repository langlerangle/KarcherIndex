module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache12800
public import KsIndexLean.AlphaLowSampleCache13056

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm75 : Finset ℤ := Finset.Ioc (-3393) (-3329)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm75
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm75)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-3329) then Cache12800.entries[(n - (-3585)).toNat]?.getD (0, 0)
  else Cache13056.entries[(n - (-3329)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm75) : (-3393) < n ∧ n ≤ (-3329) := by
  simpa only [wMm75, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm75) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm75) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm75) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-3329)
  · have hi : (n - (-3585)).toNat < 256 := by omega
    have hm : 2 * Cache12800.mode (n - (-3585)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache12800.mode]
      omega
    have hc := Cache12800.checked ⟨(n - (-3585)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-3329)).toNat < 256 := by omega
    have hm : 2 * Cache13056.mode (n - (-3329)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache13056.mode]
      omega
    have hc := Cache13056.checked ⟨(n - (-3329)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm75) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm75) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm75_c_fast : tableEnergyNumerator t wMm75 4 1 = (133081810021892723313515157244994912637349568157143095654671074589816606353454334401352037994178 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm75 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm75 4 1 =
      ∑ n ∈ wMm75, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm75_r_fast : tableEnergyRadius t wMm75 4 1 = (1515151697491864969320372399997017668960107531812078311698699954297772486038561189414630 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm75 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm75 4 1 =
      ∑ n ∈ wMm75, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm75

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm75_c : tableEnergyNumerator t wMm75 4 1 = (133081810021892723313515157244994912637349568157143095654671074589816606353454334401352037994178 : ℤ) := by
  exact KsIndex.NegSignProdFastMm75.eMm75_c_fast
theorem eMm75_r : tableEnergyRadius t wMm75 4 1 = (1515151697491864969320372399997017668960107531812078311698699954297772486038561189414630 : ℤ) := by
  exact KsIndex.NegSignProdFastMm75.eMm75_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm75_c
#print axioms KsIndex.NegSignProd.eMm75_r
