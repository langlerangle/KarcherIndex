module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache16896

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm137 : Finset ℤ := Finset.Ioc (575) (639)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm137

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm137)

def idx (n : ℤ) : ℕ := (n - (511)).toNat

lemma mem_wMm137 {n : ℤ} (hn : n ∈ wMm137) : (575) < n ∧ n ≤ (639) := by
  simpa only [wMm137, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm137) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm137 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm137) :
    2 * Cache16896.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm137 hn
  simp only [idx, Cache16896.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm137) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm137 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm137) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm137 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm137) :
    sampleNumerator (2 * n + 1) =
      (Cache16896.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache16896.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm137) :
    sampleRadius (2 * n + 1) =
      (Cache16896.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache16896.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm137_c_fast : tableEnergyNumerator t wMm137 4 1 = (48436295023699803513301875720180852581574739377295011076331647405873342019925988216547441494266365 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm137 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm137 4 1 =
      ∑ n ∈ wMm137, ((6 * n + 4) ^ 2 - 4) *
        ((Cache16896.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm137_r_fast : tableEnergyRadius t wMm137 4 1 = (171307105880705374586931259220099363111223299679375406353178223562614355109613089125519358 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm137 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm137 4 1 =
      ∑ n ∈ wMm137, (|((6 * n + 4) ^ 2 - 4)| * (Cache16896.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache16896.entries[idx n]?.getD (0, 0)).1| +
          (Cache16896.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm137

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm137_c : tableEnergyNumerator t wMm137 4 1 = (48436295023699803513301875720180852581574739377295011076331647405873342019925988216547441494266365 : ℤ) := by
  exact KsIndex.NegSignProdFastMm137.eMm137_c_fast
theorem eMm137_r : tableEnergyRadius t wMm137 4 1 = (171307105880705374586931259220099363111223299679375406353178223562614355109613089125519358 : ℤ) := by
  exact KsIndex.NegSignProdFastMm137.eMm137_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm137_c
#print axioms KsIndex.NegSignProd.eMm137_r
