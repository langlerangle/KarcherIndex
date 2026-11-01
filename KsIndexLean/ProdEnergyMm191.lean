module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache20224
public import KsIndexLean.AlphaLowSampleCache20480

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm191 : Finset ℤ := Finset.Ioc (4031) (4095)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm191
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm191)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (4095) then Cache20224.entries[(n - (3839)).toNat]?.getD (0, 0)
  else Cache20480.entries[(n - (4095)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm191) : (4031) < n ∧ n ≤ (4095) := by
  simpa only [wMm191, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm191) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm191) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm191) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (4095)
  · have hi : (n - (3839)).toNat < 256 := by omega
    have hm : 2 * Cache20224.mode (n - (3839)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache20224.mode]
      omega
    have hc := Cache20224.checked ⟨(n - (3839)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (4095)).toNat < 256 := by omega
    have hm : 2 * Cache20480.mode (n - (4095)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache20480.mode]
      omega
    have hc := Cache20480.checked ⟨(n - (4095)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm191) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm191) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm191_c_fast : tableEnergyNumerator t wMm191 4 1 = (1148952811922641622901643822145600617699289087723228097558691756822268864815076211214051030509736 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm191 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm191 4 1 =
      ∑ n ∈ wMm191, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm191_r_fast : tableEnergyRadius t wMm191 4 1 = (3654994457069442136421742764826577839096593265063427218701347600600962192688466225213490 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm191 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm191 4 1 =
      ∑ n ∈ wMm191, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm191

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm191_c : tableEnergyNumerator t wMm191 4 1 = (1148952811922641622901643822145600617699289087723228097558691756822268864815076211214051030509736 : ℤ) := by
  exact KsIndex.NegSignProdFastMm191.eMm191_c_fast
theorem eMm191_r : tableEnergyRadius t wMm191 4 1 = (3654994457069442136421742764826577839096593265063427218701347600600962192688466225213490 : ℤ) := by
  exact KsIndex.NegSignProdFastMm191.eMm191_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm191_c
#print axioms KsIndex.NegSignProd.eMm191_r
