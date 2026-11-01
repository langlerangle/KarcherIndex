module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache21504

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm208 : Finset ℤ := Finset.Ioc (5119) (5183)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm208

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm208)

def idx (n : ℤ) : ℕ := (n - (5119)).toNat

lemma mem_wMm208 {n : ℤ} (hn : n ∈ wMm208) : (5119) < n ∧ n ≤ (5183) := by
  simpa only [wMm208, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm208) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm208 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm208) :
    2 * Cache21504.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm208 hn
  simp only [idx, Cache21504.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm208) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm208 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm208) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm208 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm208) :
    sampleNumerator (2 * n + 1) =
      (Cache21504.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache21504.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm208) :
    sampleRadius (2 * n + 1) =
      (Cache21504.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache21504.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm208_c_fast : tableEnergyNumerator t wMm208 4 1 = (721870649880869254060647989723345690856360994477953222945599316716190300352906207345049254588830 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm208 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm208 4 1 =
      ∑ n ∈ wMm208, ((6 * n + 4) ^ 2 - 4) *
        ((Cache21504.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm208_r_fast : tableEnergyRadius t wMm208 4 1 = (2265639410502815425332135679073579696201662650095365294635486255164611299706304974987838 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm208 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm208 4 1 =
      ∑ n ∈ wMm208, (|((6 * n + 4) ^ 2 - 4)| * (Cache21504.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache21504.entries[idx n]?.getD (0, 0)).1| +
          (Cache21504.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm208

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm208_c : tableEnergyNumerator t wMm208 4 1 = (721870649880869254060647989723345690856360994477953222945599316716190300352906207345049254588830 : ℤ) := by
  exact KsIndex.NegSignProdFastMm208.eMm208_c_fast
theorem eMm208_r : tableEnergyRadius t wMm208 4 1 = (2265639410502815425332135679073579696201662650095365294635486255164611299706304974987838 : ℤ) := by
  exact KsIndex.NegSignProdFastMm208.eMm208_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm208_c
#print axioms KsIndex.NegSignProd.eMm208_r
