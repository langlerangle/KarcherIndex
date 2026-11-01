module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache9728
public import KsIndexLean.AlphaLowSampleCache9984

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm27 : Finset ℤ := Finset.Ioc (-6465) (-6401)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm27
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm27)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-6401) then Cache9728.entries[(n - (-6657)).toNat]?.getD (0, 0)
  else Cache9984.entries[(n - (-6401)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm27) : (-6465) < n ∧ n ≤ (-6401) := by
  simpa only [wMm27, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm27) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm27) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm27) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-6401)
  · have hi : (n - (-6657)).toNat < 256 := by omega
    have hm : 2 * Cache9728.mode (n - (-6657)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache9728.mode]
      omega
    have hc := Cache9728.checked ⟨(n - (-6657)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-6401)).toNat < 256 := by omega
    have hm : 2 * Cache9984.mode (n - (-6401)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache9984.mode]
      omega
    have hc := Cache9984.checked ⟨(n - (-6401)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm27) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm27) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm27_c_fast : tableEnergyNumerator t wMm27 4 1 = (48575686401355960968332907416213952517774777607205101426911169462332298723530794449213753319273 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm27 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm27 4 1 =
      ∑ n ∈ wMm27, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm27_r_fast : tableEnergyRadius t wMm27 4 1 = (467039653417900295898883897164391866034147110636268231870493795595061150877962611039418 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm27 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm27 4 1 =
      ∑ n ∈ wMm27, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm27

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm27_c : tableEnergyNumerator t wMm27 4 1 = (48575686401355960968332907416213952517774777607205101426911169462332298723530794449213753319273 : ℤ) := by
  exact KsIndex.NegSignProdFastMm27.eMm27_c_fast
theorem eMm27_r : tableEnergyRadius t wMm27 4 1 = (467039653417900295898883897164391866034147110636268231870493795595061150877962611039418 : ℤ) := by
  exact KsIndex.NegSignProdFastMm27.eMm27_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm27_c
#print axioms KsIndex.NegSignProd.eMm27_r
