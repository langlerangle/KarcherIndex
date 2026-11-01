module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache23552

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm240 : Finset ℤ := Finset.Ioc (7167) (7231)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm240

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm240)

def idx (n : ℤ) : ℕ := (n - (7167)).toNat

lemma mem_wMm240 {n : ℤ} (hn : n ∈ wMm240) : (7167) < n ∧ n ≤ (7231) := by
  simpa only [wMm240, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm240) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm240 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm240) :
    2 * Cache23552.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm240 hn
  simp only [idx, Cache23552.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm240) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm240 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm240) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm240 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm240) :
    sampleNumerator (2 * n + 1) =
      (Cache23552.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache23552.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm240) :
    sampleRadius (2 * n + 1) =
      (Cache23552.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache23552.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm240_c_fast : tableEnergyNumerator t wMm240 4 1 = (374990681693495707635867078674582566235648291722407614413115289189744232706388012190207118839730 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm240 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm240 4 1 =
      ∑ n ∈ wMm240, ((6 * n + 4) ^ 2 - 4) *
        ((Cache23552.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm240_r_fast : tableEnergyRadius t wMm240 4 1 = (1154678419695022622927759956151323914242325812076307115650165172118564117725387911178673 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm240 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm240 4 1 =
      ∑ n ∈ wMm240, (|((6 * n + 4) ^ 2 - 4)| * (Cache23552.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache23552.entries[idx n]?.getD (0, 0)).1| +
          (Cache23552.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm240

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm240_c : tableEnergyNumerator t wMm240 4 1 = (374990681693495707635867078674582566235648291722407614413115289189744232706388012190207118839730 : ℤ) := by
  exact KsIndex.NegSignProdFastMm240.eMm240_c_fast
theorem eMm240_r : tableEnergyRadius t wMm240 4 1 = (1154678419695022622927759956151323914242325812076307115650165172118564117725387911178673 : ℤ) := by
  exact KsIndex.NegSignProdFastMm240.eMm240_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm240_c
#print axioms KsIndex.NegSignProd.eMm240_r
