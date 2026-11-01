module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache22016

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm216 : Finset ℤ := Finset.Ioc (5631) (5695)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm216

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm216)

def idx (n : ℤ) : ℕ := (n - (5631)).toNat

lemma mem_wMm216 {n : ℤ} (hn : n ∈ wMm216) : (5631) < n ∧ n ≤ (5695) := by
  simpa only [wMm216, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm216) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm216 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm216) :
    2 * Cache22016.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm216 hn
  simp only [idx, Cache22016.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm216) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm216 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm216) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm216 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm216) :
    sampleNumerator (2 * n + 1) =
      (Cache22016.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache22016.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm216) :
    sampleRadius (2 * n + 1) =
      (Cache22016.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache22016.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm216_c_fast : tableEnergyNumerator t wMm216 4 1 = (599652860705848076531360052333174028155421915421424208821953599143576753644331011458352565728222 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm216 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm216 4 1 =
      ∑ n ∈ wMm216, ((6 * n + 4) ^ 2 - 4) *
        ((Cache22016.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm216_r_fast : tableEnergyRadius t wMm216 4 1 = (1871923216026838204570308662421034898370677745607587140631008500643384524752405596144563 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm216 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm216 4 1 =
      ∑ n ∈ wMm216, (|((6 * n + 4) ^ 2 - 4)| * (Cache22016.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache22016.entries[idx n]?.getD (0, 0)).1| +
          (Cache22016.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm216

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm216_c : tableEnergyNumerator t wMm216 4 1 = (599652860705848076531360052333174028155421915421424208821953599143576753644331011458352565728222 : ℤ) := by
  exact KsIndex.NegSignProdFastMm216.eMm216_c_fast
theorem eMm216_r : tableEnergyRadius t wMm216 4 1 = (1871923216026838204570308662421034898370677745607587140631008500643384524752405596144563 : ℤ) := by
  exact KsIndex.NegSignProdFastMm216.eMm216_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm216_c
#print axioms KsIndex.NegSignProd.eMm216_r
