module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache24064

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm248 : Finset ℤ := Finset.Ioc (7679) (7743)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm248

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm248)

def idx (n : ℤ) : ℕ := (n - (7679)).toNat

lemma mem_wMm248 {n : ℤ} (hn : n ∈ wMm248) : (7679) < n ∧ n ≤ (7743) := by
  simpa only [wMm248, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm248) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm248 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm248) :
    2 * Cache24064.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm248 hn
  simp only [idx, Cache24064.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm248) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm248 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm248) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm248 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm248) :
    sampleNumerator (2 * n + 1) =
      (Cache24064.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache24064.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm248) :
    sampleRadius (2 * n + 1) =
      (Cache24064.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache24064.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm248_c_fast : tableEnergyNumerator t wMm248 4 1 = (327860214621369618168909694414070197929613851308542698985509675494134691449113393269901982564267 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm248 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm248 4 1 =
      ∑ n ∈ wMm248, ((6 * n + 4) ^ 2 - 4) *
        ((Cache24064.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm248_r_fast : tableEnergyRadius t wMm248 4 1 = (1005595537624709232277537024989707495689411774266734908503637048970655527273861717402486 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm248 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm248 4 1 =
      ∑ n ∈ wMm248, (|((6 * n + 4) ^ 2 - 4)| * (Cache24064.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache24064.entries[idx n]?.getD (0, 0)).1| +
          (Cache24064.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm248

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm248_c : tableEnergyNumerator t wMm248 4 1 = (327860214621369618168909694414070197929613851308542698985509675494134691449113393269901982564267 : ℤ) := by
  exact KsIndex.NegSignProdFastMm248.eMm248_c_fast
theorem eMm248_r : tableEnergyRadius t wMm248 4 1 = (1005595537624709232277537024989707495689411774266734908503637048970655527273861717402486 : ℤ) := by
  exact KsIndex.NegSignProdFastMm248.eMm248_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm248_c
#print axioms KsIndex.NegSignProd.eMm248_r
