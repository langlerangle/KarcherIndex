module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache23808

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm244 : Finset ℤ := Finset.Ioc (7423) (7487)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm244

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm244)

def idx (n : ℤ) : ℕ := (n - (7423)).toNat

lemma mem_wMm244 {n : ℤ} (hn : n ∈ wMm244) : (7423) < n ∧ n ≤ (7487) := by
  simpa only [wMm244, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm244) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm244 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm244) :
    2 * Cache23808.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm244 hn
  simp only [idx, Cache23808.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm244) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm244 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm244) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm244 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm244) :
    sampleNumerator (2 * n + 1) =
      (Cache23808.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache23808.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm244) :
    sampleRadius (2 * n + 1) =
      (Cache23808.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache23808.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm244_c_fast : tableEnergyNumerator t wMm244 4 1 = (350228679324551024151044238760115300440611505276808389110242258626386757442487237665167719706567 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm244 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm244 4 1 =
      ∑ n ∈ wMm244, ((6 * n + 4) ^ 2 - 4) *
        ((Cache23808.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm244_r_fast : tableEnergyRadius t wMm244 4 1 = (1076278899205239859340405680294536295438176592795508835714748175684174129790458260459009 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm244 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm244 4 1 =
      ∑ n ∈ wMm244, (|((6 * n + 4) ^ 2 - 4)| * (Cache23808.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache23808.entries[idx n]?.getD (0, 0)).1| +
          (Cache23808.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm244

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm244_c : tableEnergyNumerator t wMm244 4 1 = (350228679324551024151044238760115300440611505276808389110242258626386757442487237665167719706567 : ℤ) := by
  exact KsIndex.NegSignProdFastMm244.eMm244_c_fast
theorem eMm244_r : tableEnergyRadius t wMm244 4 1 = (1076278899205239859340405680294536295438176592795508835714748175684174129790458260459009 : ℤ) := by
  exact KsIndex.NegSignProdFastMm244.eMm244_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm244_c
#print axioms KsIndex.NegSignProd.eMm244_r
