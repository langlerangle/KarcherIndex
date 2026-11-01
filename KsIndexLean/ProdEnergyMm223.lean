module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache22272
public import KsIndexLean.AlphaLowSampleCache22528

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm223 : Finset ℤ := Finset.Ioc (6079) (6143)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm223
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm223)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (6143) then Cache22272.entries[(n - (5887)).toNat]?.getD (0, 0)
  else Cache22528.entries[(n - (6143)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm223) : (6079) < n ∧ n ≤ (6143) := by
  simpa only [wMm223, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm223) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm223) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm223) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (6143)
  · have hi : (n - (5887)).toNat < 256 := by omega
    have hm : 2 * Cache22272.mode (n - (5887)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache22272.mode]
      omega
    have hc := Cache22272.checked ⟨(n - (5887)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (6143)).toNat < 256 := by omega
    have hm : 2 * Cache22528.mode (n - (6143)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache22528.mode]
      omega
    have hc := Cache22528.checked ⟨(n - (6143)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm223) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm223) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm223_c_fast : tableEnergyNumerator t wMm223 4 1 = (516651140546923183908242837934771459903939233217310244573743474451582934526256214278108129601518 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm223 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm223 4 1 =
      ∑ n ∈ wMm223, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm223_r_fast : tableEnergyRadius t wMm223 4 1 = (1605833933679794983684536568462449108291925997328242230757868420395411369609754178553370 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm223 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm223 4 1 =
      ∑ n ∈ wMm223, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm223

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm223_c : tableEnergyNumerator t wMm223 4 1 = (516651140546923183908242837934771459903939233217310244573743474451582934526256214278108129601518 : ℤ) := by
  exact KsIndex.NegSignProdFastMm223.eMm223_c_fast
theorem eMm223_r : tableEnergyRadius t wMm223 4 1 = (1605833933679794983684536568462449108291925997328242230757868420395411369609754178553370 : ℤ) := by
  exact KsIndex.NegSignProdFastMm223.eMm223_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm223_c
#print axioms KsIndex.NegSignProd.eMm223_r
