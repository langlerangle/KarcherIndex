module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache17408

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm145 : Finset ℤ := Finset.Ioc (1087) (1151)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm145

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm145)

def idx (n : ℤ) : ℕ := (n - (1023)).toNat

lemma mem_wMm145 {n : ℤ} (hn : n ∈ wMm145) : (1087) < n ∧ n ≤ (1151) := by
  simpa only [wMm145, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm145) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm145 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm145) :
    2 * Cache17408.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm145 hn
  simp only [idx, Cache17408.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm145) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm145 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm145) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm145 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm145) :
    sampleNumerator (2 * n + 1) =
      (Cache17408.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache17408.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm145) :
    sampleRadius (2 * n + 1) =
      (Cache17408.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache17408.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm145_c_fast : tableEnergyNumerator t wMm145 4 1 = (14479846838398069244848125547048211907758365860106369871450078976854778165071032607682805438095614 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm145 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm145 4 1 =
      ∑ n ∈ wMm145, ((6 * n + 4) ^ 2 - 4) *
        ((Cache17408.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm145_r_fast : tableEnergyRadius t wMm145 4 1 = (49515611623763620452432590690255429833805839044751668848929475304776784796399195276178422 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm145 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm145 4 1 =
      ∑ n ∈ wMm145, (|((6 * n + 4) ^ 2 - 4)| * (Cache17408.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache17408.entries[idx n]?.getD (0, 0)).1| +
          (Cache17408.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm145

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm145_c : tableEnergyNumerator t wMm145 4 1 = (14479846838398069244848125547048211907758365860106369871450078976854778165071032607682805438095614 : ℤ) := by
  exact KsIndex.NegSignProdFastMm145.eMm145_c_fast
theorem eMm145_r : tableEnergyRadius t wMm145 4 1 = (49515611623763620452432590690255429833805839044751668848929475304776784796399195276178422 : ℤ) := by
  exact KsIndex.NegSignProdFastMm145.eMm145_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm145_c
#print axioms KsIndex.NegSignProd.eMm145_r
