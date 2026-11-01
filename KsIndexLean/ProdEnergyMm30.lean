module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache9984

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm30 : Finset ℤ := Finset.Ioc (-6273) (-6209)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm30

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm30)

def idx (n : ℤ) : ℕ := (n - (-6401)).toNat

lemma mem_wMm30 {n : ℤ} (hn : n ∈ wMm30) : (-6273) < n ∧ n ≤ (-6209) := by
  simpa only [wMm30, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm30) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm30 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm30) :
    2 * Cache9984.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm30 hn
  simp only [idx, Cache9984.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm30) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm30 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm30) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm30 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm30) :
    sampleNumerator (2 * n + 1) =
      (Cache9984.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache9984.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm30) :
    sampleRadius (2 * n + 1) =
      (Cache9984.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache9984.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm30_c_fast : tableEnergyNumerator t wMm30 4 1 = (50956778403678277170519416497807822608247529867718986645031863606261045421728813378803931172616 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm30 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm30 4 1 =
      ∑ n ∈ wMm30, ((6 * n + 4) ^ 2 - 4) *
        ((Cache9984.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm30_r_fast : tableEnergyRadius t wMm30 4 1 = (493595558068077716350660206675540906491477147974102796086715252169178294138990811202487 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm30 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm30 4 1 =
      ∑ n ∈ wMm30, (|((6 * n + 4) ^ 2 - 4)| * (Cache9984.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache9984.entries[idx n]?.getD (0, 0)).1| +
          (Cache9984.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm30

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm30_c : tableEnergyNumerator t wMm30 4 1 = (50956778403678277170519416497807822608247529867718986645031863606261045421728813378803931172616 : ℤ) := by
  exact KsIndex.NegSignProdFastMm30.eMm30_c_fast
theorem eMm30_r : tableEnergyRadius t wMm30 4 1 = (493595558068077716350660206675540906491477147974102796086715252169178294138990811202487 : ℤ) := by
  exact KsIndex.NegSignProdFastMm30.eMm30_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm30_c
#print axioms KsIndex.NegSignProd.eMm30_r
