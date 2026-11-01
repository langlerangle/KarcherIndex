module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache17664
public import KsIndexLean.AlphaLowSampleCache17920

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm151 : Finset ℤ := Finset.Ioc (1471) (1535)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm151
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm151)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (1535) then Cache17664.entries[(n - (1279)).toNat]?.getD (0, 0)
  else Cache17920.entries[(n - (1535)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm151) : (1471) < n ∧ n ≤ (1535) := by
  simpa only [wMm151, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm151) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm151) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm151) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (1535)
  · have hi : (n - (1279)).toNat < 256 := by omega
    have hm : 2 * Cache17664.mode (n - (1279)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache17664.mode]
      omega
    have hc := Cache17664.checked ⟨(n - (1279)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (1535)).toNat < 256 := by omega
    have hm : 2 * Cache17920.mode (n - (1535)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache17920.mode]
      omega
    have hc := Cache17920.checked ⟨(n - (1535)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm151) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm151) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm151_c_fast : tableEnergyNumerator t wMm151 4 1 = (8099135642437504667836407094294362860105022441612554192915610093994874172273600154124716617778128 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm151 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm151 4 1 =
      ∑ n ∈ wMm151, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm151_r_fast : tableEnergyRadius t wMm151 4 1 = (27245931019997858118370665060168694772991396498051082844054052780174553118292383041731225 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm151 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm151 4 1 =
      ∑ n ∈ wMm151, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm151

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm151_c : tableEnergyNumerator t wMm151 4 1 = (8099135642437504667836407094294362860105022441612554192915610093994874172273600154124716617778128 : ℤ) := by
  exact KsIndex.NegSignProdFastMm151.eMm151_c_fast
theorem eMm151_r : tableEnergyRadius t wMm151 4 1 = (27245931019997858118370665060168694772991396498051082844054052780174553118292383041731225 : ℤ) := by
  exact KsIndex.NegSignProdFastMm151.eMm151_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm151_c
#print axioms KsIndex.NegSignProd.eMm151_r
