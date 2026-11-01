module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache11776

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm57 : Finset ℤ := Finset.Ioc (-4545) (-4481)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm57

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm57)

def idx (n : ℤ) : ℕ := (n - (-4609)).toNat

lemma mem_wMm57 {n : ℤ} (hn : n ∈ wMm57) : (-4545) < n ∧ n ≤ (-4481) := by
  simpa only [wMm57, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm57) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm57 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm57) :
    2 * Cache11776.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm57 hn
  simp only [idx, Cache11776.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm57) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm57 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm57) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm57 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm57) :
    sampleNumerator (2 * n + 1) =
      (Cache11776.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache11776.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm57) :
    sampleRadius (2 * n + 1) =
      (Cache11776.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache11776.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm57_c_fast : tableEnergyNumerator t wMm57 4 1 = (84621317495389565534194924972982519325450179349241999979726598315046629056413055491915221139349 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm57 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm57 4 1 =
      ∑ n ∈ wMm57, ((6 * n + 4) ^ 2 - 4) *
        ((Cache11776.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm57_r_fast : tableEnergyRadius t wMm57 4 1 = (889978493349815808101910983126358661047588402865392091359123996835905825316476834402017 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm57 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm57 4 1 =
      ∑ n ∈ wMm57, (|((6 * n + 4) ^ 2 - 4)| * (Cache11776.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache11776.entries[idx n]?.getD (0, 0)).1| +
          (Cache11776.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm57

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm57_c : tableEnergyNumerator t wMm57 4 1 = (84621317495389565534194924972982519325450179349241999979726598315046629056413055491915221139349 : ℤ) := by
  exact KsIndex.NegSignProdFastMm57.eMm57_c_fast
theorem eMm57_r : tableEnergyRadius t wMm57 4 1 = (889978493349815808101910983126358661047588402865392091359123996835905825316476834402017 : ℤ) := by
  exact KsIndex.NegSignProdFastMm57.eMm57_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm57_c
#print axioms KsIndex.NegSignProd.eMm57_r
