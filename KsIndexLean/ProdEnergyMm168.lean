module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache18944

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm168 : Finset ℤ := Finset.Ioc (2559) (2623)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm168

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm168)

def idx (n : ℤ) : ℕ := (n - (2559)).toNat

lemma mem_wMm168 {n : ℤ} (hn : n ∈ wMm168) : (2559) < n ∧ n ≤ (2623) := by
  simpa only [wMm168, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm168) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm168 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm168) :
    2 * Cache18944.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm168 hn
  simp only [idx, Cache18944.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm168) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm168 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm168) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm168 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm168) :
    sampleNumerator (2 * n + 1) =
      (Cache18944.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache18944.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm168) :
    sampleRadius (2 * n + 1) =
      (Cache18944.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache18944.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm168_c_fast : tableEnergyNumerator t wMm168 4 1 = (2776824261877930312426755090076613522132139874982634056830916414054070671351572505397943751302719 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm168 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm168 4 1 =
      ∑ n ∈ wMm168, ((6 * n + 4) ^ 2 - 4) *
        ((Cache18944.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm168_r_fast : tableEnergyRadius t wMm168 4 1 = (9060873731096069110312965193913885137073502702469429134630067255093322936598534044404597 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm168 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm168 4 1 =
      ∑ n ∈ wMm168, (|((6 * n + 4) ^ 2 - 4)| * (Cache18944.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache18944.entries[idx n]?.getD (0, 0)).1| +
          (Cache18944.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm168

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm168_c : tableEnergyNumerator t wMm168 4 1 = (2776824261877930312426755090076613522132139874982634056830916414054070671351572505397943751302719 : ℤ) := by
  exact KsIndex.NegSignProdFastMm168.eMm168_c_fast
theorem eMm168_r : tableEnergyRadius t wMm168 4 1 = (9060873731096069110312965193913885137073502702469429134630067255093322936598534044404597 : ℤ) := by
  exact KsIndex.NegSignProdFastMm168.eMm168_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm168_c
#print axioms KsIndex.NegSignProd.eMm168_r
