module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache24064

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm250 : Finset ℤ := Finset.Ioc (7807) (7871)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm250

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm250)

def idx (n : ℤ) : ℕ := (n - (7679)).toNat

lemma mem_wMm250 {n : ℤ} (hn : n ∈ wMm250) : (7807) < n ∧ n ≤ (7871) := by
  simpa only [wMm250, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm250) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm250 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm250) :
    2 * Cache24064.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm250 hn
  simp only [idx, Cache24064.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm250) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm250 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm250) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm250 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm250) :
    sampleNumerator (2 * n + 1) =
      (Cache24064.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache24064.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm250) :
    sampleRadius (2 * n + 1) =
      (Cache24064.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache24064.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm250_c_fast : tableEnergyNumerator t wMm250 4 1 = (317477947441848002596350193053039450022769640018928340163847011498673465395255725059391684422207 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm250 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm250 4 1 =
      ∑ n ∈ wMm250, ((6 * n + 4) ^ 2 - 4) *
        ((Cache24064.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm250_r_fast : tableEnergyRadius t wMm250 4 1 = (972835021338761899037784426851639931357434174968274627695944889563205455820761640315376 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm250 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm250 4 1 =
      ∑ n ∈ wMm250, (|((6 * n + 4) ^ 2 - 4)| * (Cache24064.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache24064.entries[idx n]?.getD (0, 0)).1| +
          (Cache24064.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm250

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm250_c : tableEnergyNumerator t wMm250 4 1 = (317477947441848002596350193053039450022769640018928340163847011498673465395255725059391684422207 : ℤ) := by
  exact KsIndex.NegSignProdFastMm250.eMm250_c_fast
theorem eMm250_r : tableEnergyRadius t wMm250 4 1 = (972835021338761899037784426851639931357434174968274627695944889563205455820761640315376 : ℤ) := by
  exact KsIndex.NegSignProdFastMm250.eMm250_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm250_c
#print axioms KsIndex.NegSignProd.eMm250_r
