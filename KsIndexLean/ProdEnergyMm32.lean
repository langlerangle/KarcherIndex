module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache10240

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm32 : Finset ℤ := Finset.Ioc (-6145) (-6081)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm32

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm32)

def idx (n : ℤ) : ℕ := (n - (-6145)).toNat

lemma mem_wMm32 {n : ℤ} (hn : n ∈ wMm32) : (-6145) < n ∧ n ≤ (-6081) := by
  simpa only [wMm32, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm32) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm32 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm32) :
    2 * Cache10240.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm32 hn
  simp only [idx, Cache10240.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm32) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm32 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm32) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm32 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm32) :
    sampleNumerator (2 * n + 1) =
      (Cache10240.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache10240.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm32) :
    sampleRadius (2 * n + 1) =
      (Cache10240.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache10240.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm32_c_fast : tableEnergyNumerator t wMm32 4 1 = (52649875098143021576182580685844851798050707718420505804296109242469761125970679681610196137317 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm32 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm32 4 1 =
      ∑ n ∈ wMm32, ((6 * n + 4) ^ 2 - 4) *
        ((Cache10240.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm32_r_fast : tableEnergyRadius t wMm32 4 1 = (512611860274497572121860729782897642201355437745558097911508967296234067006685875165633 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm32 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm32 4 1 =
      ∑ n ∈ wMm32, (|((6 * n + 4) ^ 2 - 4)| * (Cache10240.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache10240.entries[idx n]?.getD (0, 0)).1| +
          (Cache10240.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm32

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm32_c : tableEnergyNumerator t wMm32 4 1 = (52649875098143021576182580685844851798050707718420505804296109242469761125970679681610196137317 : ℤ) := by
  exact KsIndex.NegSignProdFastMm32.eMm32_c_fast
theorem eMm32_r : tableEnergyRadius t wMm32 4 1 = (512611860274497572121860729782897642201355437745558097911508967296234067006685875165633 : ℤ) := by
  exact KsIndex.NegSignProdFastMm32.eMm32_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm32_c
#print axioms KsIndex.NegSignProd.eMm32_r
