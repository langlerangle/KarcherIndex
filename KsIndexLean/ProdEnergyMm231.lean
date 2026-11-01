module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache22784
public import KsIndexLean.AlphaLowSampleCache23040

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm231 : Finset ℤ := Finset.Ioc (6591) (6655)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm231
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm231)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (6655) then Cache22784.entries[(n - (6399)).toNat]?.getD (0, 0)
  else Cache23040.entries[(n - (6655)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm231) : (6591) < n ∧ n ≤ (6655) := by
  simpa only [wMm231, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm231) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm231) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm231) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (6655)
  · have hi : (n - (6399)).toNat < 256 := by omega
    have hm : 2 * Cache22784.mode (n - (6399)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache22784.mode]
      omega
    have hc := Cache22784.checked ⟨(n - (6399)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (6655)).toNat < 256 := by omega
    have hm : 2 * Cache23040.mode (n - (6655)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache23040.mode]
      omega
    have hc := Cache23040.checked ⟨(n - (6655)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm231) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm231) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm231_c_fast : tableEnergyNumerator t wMm231 4 1 = (441412052555948392781062307813139586352845527476245273855126803861457856369933710063478499420736 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm231 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm231 4 1 =
      ∑ n ∈ wMm231, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm231_r_fast : tableEnergyRadius t wMm231 4 1 = (1365694397666907396174527772944198083020699209410353550974789910237683905851798247255165 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm231 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm231 4 1 =
      ∑ n ∈ wMm231, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm231

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm231_c : tableEnergyNumerator t wMm231 4 1 = (441412052555948392781062307813139586352845527476245273855126803861457856369933710063478499420736 : ℤ) := by
  exact KsIndex.NegSignProdFastMm231.eMm231_c_fast
theorem eMm231_r : tableEnergyRadius t wMm231 4 1 = (1365694397666907396174527772944198083020699209410353550974789910237683905851798247255165 : ℤ) := by
  exact KsIndex.NegSignProdFastMm231.eMm231_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm231_c
#print axioms KsIndex.NegSignProd.eMm231_r
