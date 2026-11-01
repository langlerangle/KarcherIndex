module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache11264
public import KsIndexLean.AlphaLowSampleCache11520

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm51 : Finset ℤ := Finset.Ioc (-4929) (-4865)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm51
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm51)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-4865) then Cache11264.entries[(n - (-5121)).toNat]?.getD (0, 0)
  else Cache11520.entries[(n - (-4865)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm51) : (-4929) < n ∧ n ≤ (-4865) := by
  simpa only [wMm51, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm51) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm51) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm51) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-4865)
  · have hi : (n - (-5121)).toNat < 256 := by omega
    have hm : 2 * Cache11264.mode (n - (-5121)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache11264.mode]
      omega
    have hc := Cache11264.checked ⟨(n - (-5121)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-4865)).toNat < 256 := by omega
    have hm : 2 * Cache11520.mode (n - (-4865)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache11520.mode]
      omega
    have hc := Cache11520.checked ⟨(n - (-4865)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm51) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm51) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm51_c_fast : tableEnergyNumerator t wMm51 4 1 = (74535549205572632678660581592460704824575794199273404585352701471187340323951978376796708925406 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm51 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm51 4 1 =
      ∑ n ∈ wMm51, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm51_r_fast : tableEnergyRadius t wMm51 4 1 = (767470221483446960669512307210180158720727571189628636807067427562031361356783055419535 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm51 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm51 4 1 =
      ∑ n ∈ wMm51, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm51

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm51_c : tableEnergyNumerator t wMm51 4 1 = (74535549205572632678660581592460704824575794199273404585352701471187340323951978376796708925406 : ℤ) := by
  exact KsIndex.NegSignProdFastMm51.eMm51_c_fast
theorem eMm51_r : tableEnergyRadius t wMm51 4 1 = (767470221483446960669512307210180158720727571189628636807067427562031361356783055419535 : ℤ) := by
  exact KsIndex.NegSignProdFastMm51.eMm51_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm51_c
#print axioms KsIndex.NegSignProd.eMm51_r
