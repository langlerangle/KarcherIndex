module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache9216
public import KsIndexLean.AlphaLowSampleCache9472

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm19 : Finset ℤ := Finset.Ioc (-6977) (-6913)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm19
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm19)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (-6913) then Cache9216.entries[(n - (-7169)).toNat]?.getD (0, 0)
  else Cache9472.entries[(n - (-6913)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm19) : (-6977) < n ∧ n ≤ (-6913) := by
  simpa only [wMm19, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm19) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm19) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm19) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (-6913)
  · have hi : (n - (-7169)).toNat < 256 := by omega
    have hm : 2 * Cache9216.mode (n - (-7169)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache9216.mode]
      omega
    have hc := Cache9216.checked ⟨(n - (-7169)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (-6913)).toNat < 256 := by omega
    have hm : 2 * Cache9472.mode (n - (-6913)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache9472.mode]
      omega
    have hc := Cache9472.checked ⟨(n - (-6913)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm19) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm19) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm19_c_fast : tableEnergyNumerator t wMm19 4 1 = (43028226084070162818858417478895606372163450228835302244791694197357990479416616758323187274912 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm19 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm19 4 1 =
      ∑ n ∈ wMm19, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm19_r_fast : tableEnergyRadius t wMm19 4 1 = (406059136028691091137856178242001614036705621101359693367843815600270299289082129689509 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm19 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm19 4 1 =
      ∑ n ∈ wMm19, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm19

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm19_c : tableEnergyNumerator t wMm19 4 1 = (43028226084070162818858417478895606372163450228835302244791694197357990479416616758323187274912 : ℤ) := by
  exact KsIndex.NegSignProdFastMm19.eMm19_c_fast
theorem eMm19_r : tableEnergyRadius t wMm19 4 1 = (406059136028691091137856178242001614036705621101359693367843815600270299289082129689509 : ℤ) := by
  exact KsIndex.NegSignProdFastMm19.eMm19_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm19_c
#print axioms KsIndex.NegSignProd.eMm19_r
