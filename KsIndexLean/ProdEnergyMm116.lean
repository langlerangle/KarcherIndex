module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache15616

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm116 : Finset ℤ := Finset.Ioc (-769) (-705)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm116

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm116)

def idx (n : ℤ) : ℕ := (n - (-769)).toNat

lemma mem_wMm116 {n : ℤ} (hn : n ∈ wMm116) : (-769) < n ∧ n ≤ (-705) := by
  simpa only [wMm116, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm116) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm116 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm116) :
    2 * Cache15616.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm116 hn
  simp only [idx, Cache15616.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm116) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm116 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm116) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm116 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm116) :
    sampleNumerator (2 * n + 1) =
      (Cache15616.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache15616.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm116) :
    sampleRadius (2 * n + 1) =
      (Cache15616.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache15616.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm116_c_fast : tableEnergyNumerator t wMm116 4 1 = (1140255810377856728323743028008711455464178423118782937951806821957517945742206237686685388767317 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm116 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm116 4 1 =
      ∑ n ∈ wMm116, ((6 * n + 4) ^ 2 - 4) *
        ((Cache15616.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm116_r_fast : tableEnergyRadius t wMm116 4 1 = (21521881015255063188199994355716106534826573092959430513654870905310531360360570725202934 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm116 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm116 4 1 =
      ∑ n ∈ wMm116, (|((6 * n + 4) ^ 2 - 4)| * (Cache15616.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache15616.entries[idx n]?.getD (0, 0)).1| +
          (Cache15616.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm116

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm116_c : tableEnergyNumerator t wMm116 4 1 = (1140255810377856728323743028008711455464178423118782937951806821957517945742206237686685388767317 : ℤ) := by
  exact KsIndex.NegSignProdFastMm116.eMm116_c_fast
theorem eMm116_r : tableEnergyRadius t wMm116 4 1 = (21521881015255063188199994355716106534826573092959430513654870905310531360360570725202934 : ℤ) := by
  exact KsIndex.NegSignProdFastMm116.eMm116_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm116_c
#print axioms KsIndex.NegSignProd.eMm116_r
