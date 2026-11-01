module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache21760

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm214 : Finset ℤ := Finset.Ioc (5503) (5567)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm214

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm214)

def idx (n : ℤ) : ℕ := (n - (5375)).toNat

lemma mem_wMm214 {n : ℤ} (hn : n ∈ wMm214) : (5503) < n ∧ n ≤ (5567) := by
  simpa only [wMm214, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm214) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm214 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm214) :
    2 * Cache21760.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm214 hn
  simp only [idx, Cache21760.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm214) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm214 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm214) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm214 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm214) :
    sampleNumerator (2 * n + 1) =
      (Cache21760.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache21760.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm214) :
    sampleRadius (2 * n + 1) =
      (Cache21760.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache21760.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm214_c_fast : tableEnergyNumerator t wMm214 4 1 = (627093950097317593256824439234727587503861813781452900353243640605975262887419959170170680959098 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm214 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm214 4 1 =
      ∑ n ∈ wMm214, ((6 * n + 4) ^ 2 - 4) *
        ((Cache21760.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm214_r_fast : tableEnergyRadius t wMm214 4 1 = (1960136636021793935735302109560981854295199678353258162061954736457631298729871571174548 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm214 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm214 4 1 =
      ∑ n ∈ wMm214, (|((6 * n + 4) ^ 2 - 4)| * (Cache21760.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache21760.entries[idx n]?.getD (0, 0)).1| +
          (Cache21760.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm214

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm214_c : tableEnergyNumerator t wMm214 4 1 = (627093950097317593256824439234727587503861813781452900353243640605975262887419959170170680959098 : ℤ) := by
  exact KsIndex.NegSignProdFastMm214.eMm214_c_fast
theorem eMm214_r : tableEnergyRadius t wMm214 4 1 = (1960136636021793935735302109560981854295199678353258162061954736457631298729871571174548 : ℤ) := by
  exact KsIndex.NegSignProdFastMm214.eMm214_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm214_c
#print axioms KsIndex.NegSignProd.eMm214_r
