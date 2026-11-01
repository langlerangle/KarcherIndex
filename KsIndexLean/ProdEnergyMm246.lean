module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache23808

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm246 : Finset ℤ := Finset.Ioc (7551) (7615)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm246

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm246)

def idx (n : ℤ) : ℕ := (n - (7423)).toNat

lemma mem_wMm246 {n : ℤ} (hn : n ∈ wMm246) : (7551) < n ∧ n ≤ (7615) := by
  simpa only [wMm246, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm246) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm246 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm246) :
    2 * Cache23808.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm246 hn
  simp only [idx, Cache23808.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm246) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm246 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm246) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm246 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm246) :
    sampleNumerator (2 * n + 1) =
      (Cache23808.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache23808.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm246) :
    sampleRadius (2 * n + 1) =
      (Cache23808.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache23808.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm246_c_fast : tableEnergyNumerator t wMm246 4 1 = (338765177314343783911912142685643471629870892001037086420467257928771556117074315018694909166182 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm246 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm246 4 1 =
      ∑ n ∈ wMm246, ((6 * n + 4) ^ 2 - 4) *
        ((Cache23808.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm246_r_fast : tableEnergyRadius t wMm246 4 1 = (1040037821695275680876206287878988902527378460143034306997538940375076010270302410896831 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm246 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm246 4 1 =
      ∑ n ∈ wMm246, (|((6 * n + 4) ^ 2 - 4)| * (Cache23808.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache23808.entries[idx n]?.getD (0, 0)).1| +
          (Cache23808.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm246

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm246_c : tableEnergyNumerator t wMm246 4 1 = (338765177314343783911912142685643471629870892001037086420467257928771556117074315018694909166182 : ℤ) := by
  exact KsIndex.NegSignProdFastMm246.eMm246_c_fast
theorem eMm246_r : tableEnergyRadius t wMm246 4 1 = (1040037821695275680876206287878988902527378460143034306997538940375076010270302410896831 : ℤ) := by
  exact KsIndex.NegSignProdFastMm246.eMm246_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm246_c
#print axioms KsIndex.NegSignProd.eMm246_r
