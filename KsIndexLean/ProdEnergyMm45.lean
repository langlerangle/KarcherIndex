module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache11008

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm45 : Finset ℤ := Finset.Ioc (-5313) (-5249)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm45

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm45)

def idx (n : ℤ) : ℕ := (n - (-5377)).toNat

lemma mem_wMm45 {n : ℤ} (hn : n ∈ wMm45) : (-5313) < n ∧ n ≤ (-5249) := by
  simpa only [wMm45, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm45) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm45 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm45) :
    2 * Cache11008.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm45 hn
  simp only [idx, Cache11008.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm45) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm45 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm45) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm45 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm45) :
    sampleNumerator (2 * n + 1) =
      (Cache11008.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache11008.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm45) :
    sampleRadius (2 * n + 1) =
      (Cache11008.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache11008.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm45_c_fast : tableEnergyNumerator t wMm45 4 1 = (66249418334833702639177771755079555734628117011985800211254896106566207729288773303229734825891 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm45 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm45 4 1 =
      ∑ n ∈ wMm45, ((6 * n + 4) ^ 2 - 4) *
        ((Cache11008.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm45_r_fast : tableEnergyRadius t wMm45 4 1 = (669108746990497812205969849687383993332820195157029516677886608670905053946566697462625 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm45 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm45 4 1 =
      ∑ n ∈ wMm45, (|((6 * n + 4) ^ 2 - 4)| * (Cache11008.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache11008.entries[idx n]?.getD (0, 0)).1| +
          (Cache11008.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm45

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm45_c : tableEnergyNumerator t wMm45 4 1 = (66249418334833702639177771755079555734628117011985800211254896106566207729288773303229734825891 : ℤ) := by
  exact KsIndex.NegSignProdFastMm45.eMm45_c_fast
theorem eMm45_r : tableEnergyRadius t wMm45 4 1 = (669108746990497812205969849687383993332820195157029516677886608670905053946566697462625 : ℤ) := by
  exact KsIndex.NegSignProdFastMm45.eMm45_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm45_c
#print axioms KsIndex.NegSignProd.eMm45_r
