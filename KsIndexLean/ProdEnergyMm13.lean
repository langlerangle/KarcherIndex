module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache8960

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm13 : Finset ℤ := Finset.Ioc (-7361) (-7297)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm13

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm13)

def idx (n : ℤ) : ℕ := (n - (-7425)).toNat

lemma mem_wMm13 {n : ℤ} (hn : n ∈ wMm13) : (-7361) < n ∧ n ≤ (-7297) := by
  simpa only [wMm13, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm13) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm13 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm13) :
    2 * Cache8960.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm13 hn
  simp only [idx, Cache8960.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm13) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm13 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm13) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm13 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm13) :
    sampleNumerator (2 * n + 1) =
      (Cache8960.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache8960.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm13) :
    sampleRadius (2 * n + 1) =
      (Cache8960.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache8960.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm13_c_fast : tableEnergyNumerator t wMm13 4 1 = (39502660903297923704408537063190258461073441150563817695135929259529351121240542150806944138311 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm13 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm13 4 1 =
      ∑ n ∈ wMm13, ((6 * n + 4) ^ 2 - 4) *
        ((Cache8960.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm13_r_fast : tableEnergyRadius t wMm13 4 1 = (367988560946454848314833550900086519085940203480805106960596895272200413799622820462123 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm13 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm13 4 1 =
      ∑ n ∈ wMm13, (|((6 * n + 4) ^ 2 - 4)| * (Cache8960.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache8960.entries[idx n]?.getD (0, 0)).1| +
          (Cache8960.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm13

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm13_c : tableEnergyNumerator t wMm13 4 1 = (39502660903297923704408537063190258461073441150563817695135929259529351121240542150806944138311 : ℤ) := by
  exact KsIndex.NegSignProdFastMm13.eMm13_c_fast
theorem eMm13_r : tableEnergyRadius t wMm13 4 1 = (367988560946454848314833550900086519085940203480805106960596895272200413799622820462123 : ℤ) := by
  exact KsIndex.NegSignProdFastMm13.eMm13_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm13_c
#print axioms KsIndex.NegSignProd.eMm13_r
