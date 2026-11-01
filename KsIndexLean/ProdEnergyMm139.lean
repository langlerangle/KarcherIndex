module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache16896
public import KsIndexLean.AlphaLowSampleCache17152

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm139 : Finset ℤ := Finset.Ioc (703) (767)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm139
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm139)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (767) then Cache16896.entries[(n - (511)).toNat]?.getD (0, 0)
  else Cache17152.entries[(n - (767)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm139) : (703) < n ∧ n ≤ (767) := by
  simpa only [wMm139, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm139) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm139) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm139) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (767)
  · have hi : (n - (511)).toNat < 256 := by omega
    have hm : 2 * Cache16896.mode (n - (511)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache16896.mode]
      omega
    have hc := Cache16896.checked ⟨(n - (511)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (767)).toNat < 256 := by omega
    have hm : 2 * Cache17152.mode (n - (767)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache17152.mode]
      omega
    have hc := Cache17152.checked ⟨(n - (767)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm139) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm139) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm139_c_fast : tableEnergyNumerator t wMm139 4 1 = (33182449200948699869282700019879581571880970529604019906808773461733054884487837739249703262042635 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm139 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm139 4 1 =
      ∑ n ∈ wMm139, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm139_r_fast : tableEnergyRadius t wMm139 4 1 = (116132579707371119114254134669978528503546584034137729485200269478465169392459707657526136 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm139 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm139 4 1 =
      ∑ n ∈ wMm139, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm139

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm139_c : tableEnergyNumerator t wMm139 4 1 = (33182449200948699869282700019879581571880970529604019906808773461733054884487837739249703262042635 : ℤ) := by
  exact KsIndex.NegSignProdFastMm139.eMm139_c_fast
theorem eMm139_r : tableEnergyRadius t wMm139 4 1 = (116132579707371119114254134669978528503546584034137729485200269478465169392459707657526136 : ℤ) := by
  exact KsIndex.NegSignProdFastMm139.eMm139_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm139_c
#print axioms KsIndex.NegSignProd.eMm139_r
