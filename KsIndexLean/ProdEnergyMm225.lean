module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache22528

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm225 : Finset ℤ := Finset.Ioc (6207) (6271)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm225

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm225)

def idx (n : ℤ) : ℕ := (n - (6143)).toNat

lemma mem_wMm225 {n : ℤ} (hn : n ∈ wMm225) : (6207) < n ∧ n ≤ (6271) := by
  simpa only [wMm225, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm225) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm225 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm225) :
    2 * Cache22528.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm225 hn
  simp only [idx, Cache22528.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm225) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm225 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm225) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm225 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm225) :
    sampleNumerator (2 * n + 1) =
      (Cache22528.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache22528.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm225) :
    sampleRadius (2 * n + 1) =
      (Cache22528.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache22528.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm225_c_fast : tableEnergyNumerator t wMm225 4 1 = (496117445914946881464630263866300627067363357368989834648001066819408421154786835193719167180309 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm225 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm225 4 1 =
      ∑ n ∈ wMm225, ((6 * n + 4) ^ 2 - 4) *
        ((Cache22528.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm225_r_fast : tableEnergyRadius t wMm225 4 1 = (1540189716874904210710317792070662877009515487241338395066903205535686063226605173279794 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm225 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm225 4 1 =
      ∑ n ∈ wMm225, (|((6 * n + 4) ^ 2 - 4)| * (Cache22528.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache22528.entries[idx n]?.getD (0, 0)).1| +
          (Cache22528.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm225

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm225_c : tableEnergyNumerator t wMm225 4 1 = (496117445914946881464630263866300627067363357368989834648001066819408421154786835193719167180309 : ℤ) := by
  exact KsIndex.NegSignProdFastMm225.eMm225_c_fast
theorem eMm225_r : tableEnergyRadius t wMm225 4 1 = (1540189716874904210710317792070662877009515487241338395066903205535686063226605173279794 : ℤ) := by
  exact KsIndex.NegSignProdFastMm225.eMm225_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm225_c
#print axioms KsIndex.NegSignProd.eMm225_r
