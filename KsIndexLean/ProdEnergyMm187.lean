module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache19968
public import KsIndexLean.AlphaLowSampleCache20224

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm187 : Finset ℤ := Finset.Ioc (3775) (3839)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm187
open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm187)

def cacheEntry (n : ℤ) : ℤ × ℤ :=
  if n < (3839) then Cache19968.entries[(n - (3583)).toNat]?.getD (0, 0)
  else Cache20224.entries[(n - (3839)).toNat]?.getD (0, 0)

lemma mem_window {n : ℤ} (hn : n ∈ wMm187) : (3775) < n ∧ n ≤ (3839) := by
  simpa only [wMm187, Finset.mem_Ioc] using hn

lemma covLow {n : ℤ} (hn : n ∈ wMm187) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm187) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_window hn
  exact sampleCovered_of_bound (by omega)

lemma sample_cache {n : ℤ} (hn : n ∈ wMm187) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 ∧
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := by
  obtain ⟨h1, h2⟩ := mem_window hn
  by_cases h : n < (3839)
  · have hi : (n - (3583)).toNat < 256 := by omega
    have hm : 2 * Cache19968.mode (n - (3583)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache19968.mode]
      omega
    have hc := Cache19968.checked ⟨(n - (3583)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_pos h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩
  · have hi : (n - (3839)).toNat < 256 := by omega
    have hm : 2 * Cache20224.mode (n - (3839)).toNat + 1 = 2 * n + 1 := by
      simp only [Cache20224.mode]
      omega
    have hc := Cache20224.checked ⟨(n - (3839)).toNat, hi⟩
    rw [hm] at hc
    simp only [cacheEntry, if_neg h]
    exact ⟨(hc.1.trans (tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm,
      (hc.2.trans (tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn))).symm⟩

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm187) :
    sampleNumerator (2 * n + 1) = (cacheEntry n).1 := (sample_cache hn).1
lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm187) :
    sampleRadius (2 * n + 1) = (cacheEntry n).2 := (sample_cache hn).2

theorem eMm187_c_fast : tableEnergyNumerator t wMm187 4 1 = (1305267311772045098481432656880916032440454849833113593307862025123023032692464092605093190852619 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm187 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm187 4 1 =
      ∑ n ∈ wMm187, ((6 * n + 4) ^ 2 - 4) *
        ((cacheEntry n).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm187_r_fast : tableEnergyRadius t wMm187 4 1 = (4167597204995957115609545250973155623845622558765976201529074465228303890157681029141869 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm187 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm187 4 1 =
      ∑ n ∈ wMm187, (|((6 * n + 4) ^ 2 - 4)| * (cacheEntry n).2 *
        (2 * |(cacheEntry n).1| +
          (cacheEntry n).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm187

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm187_c : tableEnergyNumerator t wMm187 4 1 = (1305267311772045098481432656880916032440454849833113593307862025123023032692464092605093190852619 : ℤ) := by
  exact KsIndex.NegSignProdFastMm187.eMm187_c_fast
theorem eMm187_r : tableEnergyRadius t wMm187 4 1 = (4167597204995957115609545250973155623845622558765976201529074465228303890157681029141869 : ℤ) := by
  exact KsIndex.NegSignProdFastMm187.eMm187_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm187_c
#print axioms KsIndex.NegSignProd.eMm187_r
