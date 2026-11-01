module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache9472
public import KsIndexLean.AlphaLowSampleCache9728

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm23 : Finset ℤ := Finset.Ioc (-6721) (-6657)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm23
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm23)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-6657) then Cache9472.entries[(n - (-6913)).toNat]?.getD (0, 0)
  else Cache9728.entries[(n - (-6657)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm23) : (-6721) < n ∧ n ≤ (-6657) := by
  simpa only [wMm23, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm23) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm23) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm23) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-6657)
  · have hi : (n - (-6913)).toNat < 256 := by omega
    have hm : 2 * Cache9472.mode (n - (-6913)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache9472.mode]
      omega
    have hc := Cache9472.checked ⟨(n - (-6913)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-6657)).toNat < 256 := by omega
    have hm : 2 * Cache9728.mode (n - (-6657)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache9728.mode]
      omega
    have hc := Cache9728.checked ⟨(n - (-6657)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm23) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm23) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm23_c_fast : tableEnergyNumerator t wMm23 4 1 = (45667455554199048948929510213609703409136116333346706947036918528864320548910053984525898289961 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm23 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm23 4 1 =
      ∑ n ∈ wMm23, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm23_r_fast : tableEnergyRadius t wMm23 4 1 = (434911794037508426860835527889009764985708661048678411212963425798190799209191710149583 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm23 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm23 4 1 =
      ∑ n ∈ wMm23, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm23

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm23_c : tableEnergyNumerator t wMm23 4 1 = (45667455554199048948929510213609703409136116333346706947036918528864320548910053984525898289961 : ℤ) := by
  exact KsIndex.NegSignProdFastMm23.eMm23_c_fast
theorem eMm23_r : tableEnergyRadius t wMm23 4 1 = (434911794037508426860835527889009764985708661048678411212963425798190799209191710149583 : ℤ) := by
  exact KsIndex.NegSignProdFastMm23.eMm23_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm23_c
#print axioms KsIndex.NegSignProd.eMm23_r
