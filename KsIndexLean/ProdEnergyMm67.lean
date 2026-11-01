module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache12288
public import KsIndexLean.AlphaLowSampleCache12544

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm67 : Finset ℤ := Finset.Ioc (-3905) (-3841)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm67
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm67)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-3841) then Cache12288.entries[(n - (-4097)).toNat]?.getD (0, 0)
  else Cache12544.entries[(n - (-3841)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm67) : (-3905) < n ∧ n ≤ (-3841) := by
  simpa only [wMm67, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm67) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm67) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm67) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-3841)
  · have hi : (n - (-4097)).toNat < 256 := by omega
    have hm : 2 * Cache12288.mode (n - (-4097)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache12288.mode]
      omega
    have hc := Cache12288.checked ⟨(n - (-4097)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-3841)).toNat < 256 := by omega
    have hm : 2 * Cache12544.mode (n - (-3841)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache12544.mode]
      omega
    have hc := Cache12544.checked ⟨(n - (-3841)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm67) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm67) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm67_c_fast : tableEnergyNumerator t wMm67 4 1 = (107146612530990866061849793562537995309221295629751363878522756157113461366358869005827623838082 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm67 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm67 4 1 =
      ∑ n ∈ wMm67, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm67_r_fast : tableEnergyRadius t wMm67 4 1 = (1173545283360485371419757803230191489525067862965982245776750176741994570893790958354231 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm67 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm67 4 1 =
      ∑ n ∈ wMm67, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm67

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm67_c : tableEnergyNumerator t wMm67 4 1 = (107146612530990866061849793562537995309221295629751363878522756157113461366358869005827623838082 : ℤ) := by
  exact KsIndex.NegSignProdFastMm67.eMm67_c_fast
theorem eMm67_r : tableEnergyRadius t wMm67 4 1 = (1173545283360485371419757803230191489525067862965982245776750176741994570893790958354231 : ℤ) := by
  exact KsIndex.NegSignProdFastMm67.eMm67_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm67_c
#print axioms KsIndex.NegSignProd.eMm67_r
