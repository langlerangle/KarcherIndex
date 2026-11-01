module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache10240
public import KsIndexLean.AlphaLowSampleCache10496

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm35 : Finset ℤ := Finset.Ioc (-5953) (-5889)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm35
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm35)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-5889) then Cache10240.entries[(n - (-6145)).toNat]?.getD (0, 0)
  else Cache10496.entries[(n - (-5889)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm35) : (-5953) < n ∧ n ≤ (-5889) := by
  simpa only [wMm35, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm35) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm35) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm35) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-5889)
  · have hi : (n - (-6145)).toNat < 256 := by omega
    have hm : 2 * Cache10240.mode (n - (-6145)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache10240.mode]
      omega
    have hc := Cache10240.checked ⟨(n - (-6145)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-5889)).toNat < 256 := by omega
    have hm : 2 * Cache10496.mode (n - (-5889)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache10496.mode]
      omega
    have hc := Cache10496.checked ⟨(n - (-5889)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm35) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm35) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm35_c_fast : tableEnergyNumerator t wMm35 4 1 = (55364111532850520406498097419276092979387750817654344096193077399667136065731040753475388775930 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm35 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm35 4 1 =
      ∑ n ∈ wMm35, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm35_r_fast : tableEnergyRadius t wMm35 4 1 = (543322198157678657769950224191973045372710914210082711117759683782623773307035857483830 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm35 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm35 4 1 =
      ∑ n ∈ wMm35, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm35

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm35_c : tableEnergyNumerator t wMm35 4 1 = (55364111532850520406498097419276092979387750817654344096193077399667136065731040753475388775930 : ℤ) := by
  exact KsIndex.NegSignProdFastMm35.eMm35_c_fast
theorem eMm35_r : tableEnergyRadius t wMm35 4 1 = (543322198157678657769950224191973045372710914210082711117759683782623773307035857483830 : ℤ) := by
  exact KsIndex.NegSignProdFastMm35.eMm35_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm35_c
#print axioms KsIndex.NegSignProd.eMm35_r
