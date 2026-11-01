module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache21504

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm210 : Finset ℤ := Finset.Ioc (5247) (5311)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm210

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm210)

def idx (n : ℤ) : ℕ := (n - (5119)).toNat

lemma mem_wMm210 {n : ℤ} (hn : n ∈ wMm210) : (5247) < n ∧ n ≤ (5311) := by
  simpa only [wMm210, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm210) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm210 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm210) :
    2 * Cache21504.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm210 hn
  simp only [idx, Cache21504.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm210) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm210 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm210) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm210 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm210) :
    sampleNumerator (2 * n + 1) =
      (Cache21504.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache21504.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm210) :
    sampleRadius (2 * n + 1) =
      (Cache21504.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache21504.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm210_c_fast : tableEnergyNumerator t wMm210 4 1 = (688001864363111962340471572215054160576938693346616578919708244633864888125191274326786140211182 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm210 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm210 4 1 =
      ∑ n ∈ wMm210, ((6 * n + 4) ^ 2 - 4) *
        ((Cache21504.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm210_r_fast : tableEnergyRadius t wMm210 4 1 = (2156325661601765249508750971893898339496040609782348453620343036871286623466922893206733 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm210 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm210 4 1 =
      ∑ n ∈ wMm210, (|((6 * n + 4) ^ 2 - 4)| * (Cache21504.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache21504.entries[idx n]?.getD (0, 0)).1| +
          (Cache21504.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm210

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm210_c : tableEnergyNumerator t wMm210 4 1 = (688001864363111962340471572215054160576938693346616578919708244633864888125191274326786140211182 : ℤ) := by
  exact KsIndex.NegSignProdFastMm210.eMm210_c_fast
theorem eMm210_r : tableEnergyRadius t wMm210 4 1 = (2156325661601765249508750971893898339496040609782348453620343036871286623466922893206733 : ℤ) := by
  exact KsIndex.NegSignProdFastMm210.eMm210_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm210_c
#print axioms KsIndex.NegSignProd.eMm210_r
