module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache11776

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm56 : Finset ℤ := Finset.Ioc (-4609) (-4545)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm56

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm56)

def idx (n : ℤ) : ℕ := (n - (-4609)).toNat

lemma mem_wMm56 {n : ℤ} (hn : n ∈ wMm56) : (-4609) < n ∧ n ≤ (-4545) := by
  simpa only [wMm56, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm56) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm56 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm56) :
    2 * Cache11776.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm56 hn
  simp only [idx, Cache11776.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm56) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm56 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm56) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm56 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm56) :
    sampleNumerator (2 * n + 1) =
      (Cache11776.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache11776.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm56) :
    sampleRadius (2 * n + 1) =
      (Cache11776.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache11776.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm56_c_fast : tableEnergyNumerator t wMm56 4 1 = (82793101691663011561167952501352333471518655090968644779937194805800432033652109334919525378803 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm56 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm56 4 1 =
      ∑ n ∈ wMm56, ((6 * n + 4) ^ 2 - 4) *
        ((Cache11776.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm56_r_fast : tableEnergyRadius t wMm56 4 1 = (867555092327449504504625940192080350714554572587887909407675090111023286681917857933761 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm56 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm56 4 1 =
      ∑ n ∈ wMm56, (|((6 * n + 4) ^ 2 - 4)| * (Cache11776.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache11776.entries[idx n]?.getD (0, 0)).1| +
          (Cache11776.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm56

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm56_c : tableEnergyNumerator t wMm56 4 1 = (82793101691663011561167952501352333471518655090968644779937194805800432033652109334919525378803 : ℤ) := by
  exact KsIndex.NegSignProdFastMm56.eMm56_c_fast
theorem eMm56_r : tableEnergyRadius t wMm56 4 1 = (867555092327449504504625940192080350714554572587887909407675090111023286681917857933761 : ℤ) := by
  exact KsIndex.NegSignProdFastMm56.eMm56_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm56_c
#print axioms KsIndex.NegSignProd.eMm56_r
