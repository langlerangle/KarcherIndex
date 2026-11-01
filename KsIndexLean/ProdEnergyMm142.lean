module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache17152

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm142 : Finset ℤ := Finset.Ioc (895) (959)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm142

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm142)

def idx (n : ℤ) : ℕ := (n - (767)).toNat

lemma mem_wMm142 {n : ℤ} (hn : n ∈ wMm142) : (895) < n ∧ n ≤ (959) := by
  simpa only [wMm142, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm142) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm142 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm142) :
    2 * Cache17152.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm142 hn
  simp only [idx, Cache17152.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm142) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm142 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm142) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm142 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm142) :
    sampleNumerator (2 * n + 1) =
      (Cache17152.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache17152.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm142) :
    sampleRadius (2 * n + 1) =
      (Cache17152.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache17152.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm142_c_fast : tableEnergyNumerator t wMm142 4 1 = (20986843546411189288105911472040641547204912019292044517906763641496413292596691636054998746735905 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm142 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm142 4 1 =
      ∑ n ∈ wMm142, ((6 * n + 4) ^ 2 - 4) *
        ((Cache17152.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm142_r_fast : tableEnergyRadius t wMm142 4 1 = (72517638285675086666676291078202902884555248029374691872979060828393376879867521785986376 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm142 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm142 4 1 =
      ∑ n ∈ wMm142, (|((6 * n + 4) ^ 2 - 4)| * (Cache17152.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache17152.entries[idx n]?.getD (0, 0)).1| +
          (Cache17152.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm142

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm142_c : tableEnergyNumerator t wMm142 4 1 = (20986843546411189288105911472040641547204912019292044517906763641496413292596691636054998746735905 : ℤ) := by
  exact KsIndex.NegSignProdFastMm142.eMm142_c_fast
theorem eMm142_r : tableEnergyRadius t wMm142 4 1 = (72517638285675086666676291078202902884555248029374691872979060828393376879867521785986376 : ℤ) := by
  exact KsIndex.NegSignProdFastMm142.eMm142_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm142_c
#print axioms KsIndex.NegSignProd.eMm142_r
