module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache9216

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm18 : Finset ℤ := Finset.Ioc (-7041) (-6977)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm18

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm18)

def idx (n : ℤ) : ℕ := (n - (-7169)).toNat

lemma mem_wMm18 {n : ℤ} (hn : n ∈ wMm18) : (-7041) < n ∧ n ≤ (-6977) := by
  simpa only [wMm18, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm18) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm18 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm18) :
    2 * Cache9216.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm18 hn
  simp only [idx, Cache9216.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm18) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm18 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm18) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm18 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm18) :
    sampleNumerator (2 * n + 1) =
      (Cache9216.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache9216.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm18) :
    sampleRadius (2 * n + 1) =
      (Cache9216.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache9216.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm18_c_fast : tableEnergyNumerator t wMm18 4 1 = (42406447692571179977591519137259344860274834333473271227533588014638087200496942876620655779348 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm18 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm18 4 1 =
      ∑ n ∈ wMm18, ((6 * n + 4) ^ 2 - 4) *
        ((Cache9216.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm18_r_fast : tableEnergyRadius t wMm18 4 1 = (399305046529722775773965952908493454874018090014499124879771196413197979988486096254190 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm18 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm18 4 1 =
      ∑ n ∈ wMm18, (|((6 * n + 4) ^ 2 - 4)| * (Cache9216.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache9216.entries[idx n]?.getD (0, 0)).1| +
          (Cache9216.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm18

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm18_c : tableEnergyNumerator t wMm18 4 1 = (42406447692571179977591519137259344860274834333473271227533588014638087200496942876620655779348 : ℤ) := by
  exact KsIndex.NegSignProdFastMm18.eMm18_c_fast
theorem eMm18_r : tableEnergyRadius t wMm18 4 1 = (399305046529722775773965952908493454874018090014499124879771196413197979988486096254190 : ℤ) := by
  exact KsIndex.NegSignProdFastMm18.eMm18_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm18_c
#print axioms KsIndex.NegSignProd.eMm18_r
