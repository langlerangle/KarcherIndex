module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache20224

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm190 : Finset ℤ := Finset.Ioc (3967) (4031)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm190

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm190)

def idx (n : ℤ) : ℕ := (n - (3839)).toNat

lemma mem_wMm190 {n : ℤ} (hn : n ∈ wMm190) : (3967) < n ∧ n ≤ (4031) := by
  simpa only [wMm190, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm190) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm190 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm190) :
    2 * Cache20224.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm190 hn
  simp only [idx, Cache20224.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm190) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm190 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm190) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm190 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm190) :
    sampleNumerator (2 * n + 1) =
      (Cache20224.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache20224.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm190) :
    sampleRadius (2 * n + 1) =
      (Cache20224.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache20224.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm190_c_fast : tableEnergyNumerator t wMm190 4 1 = (1185266026331697672299248999202366221150883929097853812173275356010765835519569355489386528298250 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm190 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm190 4 1 =
      ∑ n ∈ wMm190, ((6 * n + 4) ^ 2 - 4) *
        ((Cache20224.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm190_r_fast : tableEnergyRadius t wMm190 4 1 = (3773907821094662186100270803074322815632985113150092046480203052765852078566534120384705 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm190 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm190 4 1 =
      ∑ n ∈ wMm190, (|((6 * n + 4) ^ 2 - 4)| * (Cache20224.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache20224.entries[idx n]?.getD (0, 0)).1| +
          (Cache20224.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm190

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm190_c : tableEnergyNumerator t wMm190 4 1 = (1185266026331697672299248999202366221150883929097853812173275356010765835519569355489386528298250 : ℤ) := by
  exact KsIndex.NegSignProdFastMm190.eMm190_c_fast
theorem eMm190_r : tableEnergyRadius t wMm190 4 1 = (3773907821094662186100270803074322815632985113150092046480203052765852078566534120384705 : ℤ) := by
  exact KsIndex.NegSignProdFastMm190.eMm190_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm190_c
#print axioms KsIndex.NegSignProd.eMm190_r
