module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache10240

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm33 : Finset ℤ := Finset.Ioc (-6081) (-6017)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm33

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm33)

def idx (n : ℤ) : ℕ := (n - (-6145)).toNat

lemma mem_wMm33 {n : ℤ} (hn : n ∈ wMm33) : (-6081) < n ∧ n ≤ (-6017) := by
  simpa only [wMm33, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm33) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm33 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm33) :
    2 * Cache10240.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm33 hn
  simp only [idx, Cache10240.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm33) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm33 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm33) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm33 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm33) :
    sampleNumerator (2 * n + 1) =
      (Cache10240.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache10240.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm33) :
    sampleRadius (2 * n + 1) =
      (Cache10240.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache10240.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm33_c_fast : tableEnergyNumerator t wMm33 4 1 = (53530483085624074023540841015668535505599664048492217216232765627867681042851661272929930391452 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm33 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm33 4 1 =
      ∑ n ∈ wMm33, ((6 * n + 4) ^ 2 - 4) *
        ((Cache10240.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm33_r_fast : tableEnergyRadius t wMm33 4 1 = (522545495752703315649500049373445616283871753526800408670247295927007430187444052966968 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm33 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm33 4 1 =
      ∑ n ∈ wMm33, (|((6 * n + 4) ^ 2 - 4)| * (Cache10240.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache10240.entries[idx n]?.getD (0, 0)).1| +
          (Cache10240.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm33

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm33_c : tableEnergyNumerator t wMm33 4 1 = (53530483085624074023540841015668535505599664048492217216232765627867681042851661272929930391452 : ℤ) := by
  exact KsIndex.NegSignProdFastMm33.eMm33_c_fast
theorem eMm33_r : tableEnergyRadius t wMm33 4 1 = (522545495752703315649500049373445616283871753526800408670247295927007430187444052966968 : ℤ) := by
  exact KsIndex.NegSignProdFastMm33.eMm33_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm33_c
#print axioms KsIndex.NegSignProd.eMm33_r
