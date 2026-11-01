module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache24064

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm249 : Finset ℤ := Finset.Ioc (7743) (7807)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm249

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm249)

def idx (n : ℤ) : ℕ := (n - (7679)).toNat

lemma mem_wMm249 {n : ℤ} (hn : n ∈ wMm249) : (7743) < n ∧ n ≤ (7807) := by
  simpa only [wMm249, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm249) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm249 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm249) :
    2 * Cache24064.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm249 hn
  simp only [idx, Cache24064.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm249) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm249 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm249) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm249 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm249) :
    sampleNumerator (2 * n + 1) =
      (Cache24064.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache24064.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm249) :
    sampleRadius (2 * n + 1) =
      (Cache24064.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache24064.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm249_c_fast : tableEnergyNumerator t wMm249 4 1 = (322605870290014636138980897455198745286934092558527779402018423353493403795315195269660695518238 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm249 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm249 4 1 =
      ∑ n ∈ wMm249, ((6 * n + 4) ^ 2 - 4) *
        ((Cache24064.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm249_r_fast : tableEnergyRadius t wMm249 4 1 = (989011996144153714041725061417985637872901739781262293438375510621977189253071203534484 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm249 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm249 4 1 =
      ∑ n ∈ wMm249, (|((6 * n + 4) ^ 2 - 4)| * (Cache24064.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache24064.entries[idx n]?.getD (0, 0)).1| +
          (Cache24064.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm249

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm249_c : tableEnergyNumerator t wMm249 4 1 = (322605870290014636138980897455198745286934092558527779402018423353493403795315195269660695518238 : ℤ) := by
  exact KsIndex.NegSignProdFastMm249.eMm249_c_fast
theorem eMm249_r : tableEnergyRadius t wMm249 4 1 = (989011996144153714041725061417985637872901739781262293438375510621977189253071203534484 : ℤ) := by
  exact KsIndex.NegSignProdFastMm249.eMm249_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm249_c
#print axioms KsIndex.NegSignProd.eMm249_r
