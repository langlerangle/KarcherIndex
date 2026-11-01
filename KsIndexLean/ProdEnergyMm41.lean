module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache10752

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm41 : Finset ℤ := Finset.Ioc (-5569) (-5505)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm41

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm41)

def idx (n : ℤ) : ℕ := (n - (-5633)).toNat

lemma mem_wMm41 {n : ℤ} (hn : n ∈ wMm41) : (-5569) < n ∧ n ≤ (-5505) := by
  simpa only [wMm41, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm41) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm41 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm41) :
    2 * Cache10752.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm41 hn
  simp only [idx, Cache10752.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm41) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm41 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm41) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm41 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm41) :
    sampleNumerator (2 * n + 1) =
      (Cache10752.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache10752.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm41) :
    sampleRadius (2 * n + 1) =
      (Cache10752.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache10752.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm41_c_fast : tableEnergyNumerator t wMm41 4 1 = (61514927190802881654544352771801048390807312600013600435641578113896843518841016173018828611240 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm41 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm41 4 1 =
      ∑ n ∈ wMm41, ((6 * n + 4) ^ 2 - 4) *
        ((Cache10752.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm41_r_fast : tableEnergyRadius t wMm41 4 1 = (613899214568806408057360842417063873540283460785150124917959531905183072638431324082294 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm41 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm41 4 1 =
      ∑ n ∈ wMm41, (|((6 * n + 4) ^ 2 - 4)| * (Cache10752.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache10752.entries[idx n]?.getD (0, 0)).1| +
          (Cache10752.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm41

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm41_c : tableEnergyNumerator t wMm41 4 1 = (61514927190802881654544352771801048390807312600013600435641578113896843518841016173018828611240 : ℤ) := by
  exact KsIndex.NegSignProdFastMm41.eMm41_c_fast
theorem eMm41_r : tableEnergyRadius t wMm41 4 1 = (613899214568806408057360842417063873540283460785150124917959531905183072638431324082294 : ℤ) := by
  exact KsIndex.NegSignProdFastMm41.eMm41_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm41_c
#print axioms KsIndex.NegSignProd.eMm41_r
