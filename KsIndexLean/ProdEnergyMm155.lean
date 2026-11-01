module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache17920
public import KsIndexLean.AlphaLowSampleCache18176

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm155 : Finset ℤ := Finset.Ioc (1727) (1791)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm155
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm155)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (1791) then Cache17920.entries[(n - (1535)).toNat]?.getD (0, 0)
  else Cache18176.entries[(n - (1791)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm155) : (1727) < n ∧ n ≤ (1791) := by
  simpa only [wMm155, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm155) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm155) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm155) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (1791)
  · have hi : (n - (1535)).toNat < 256 := by omega
    have hm : 2 * Cache17920.mode (n - (1535)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache17920.mode]
      omega
    have hc := Cache17920.checked ⟨(n - (1535)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (1791)).toNat < 256 := by omega
    have hm : 2 * Cache18176.mode (n - (1791)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache18176.mode]
      omega
    have hc := Cache18176.checked ⟨(n - (1791)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm155) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm155) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm155_c_fast : tableEnergyNumerator t wMm155 4 1 = (5943743651114403707389301525209857184827747712929115275365454393117454452784391321721132414664234 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm155 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm155 4 1 =
      ∑ n ∈ wMm155, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm155_r_fast : tableEnergyRadius t wMm155 4 1 = (19820424363904303314223510176410774435408422767324042483228507554910492458427683965241144 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm155 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm155 4 1 =
      ∑ n ∈ wMm155, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm155

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm155_c : tableEnergyNumerator t wMm155 4 1 = (5943743651114403707389301525209857184827747712929115275365454393117454452784391321721132414664234 : ℤ) := by
  exact KsIndex.NegSignProdFastMm155.eMm155_c_fast
theorem eMm155_r : tableEnergyRadius t wMm155 4 1 = (19820424363904303314223510176410774435408422767324042483228507554910492458427683965241144 : ℤ) := by
  exact KsIndex.NegSignProdFastMm155.eMm155_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm155_c
#print axioms KsIndex.NegSignProd.eMm155_r
