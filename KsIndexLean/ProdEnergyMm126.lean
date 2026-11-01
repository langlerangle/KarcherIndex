module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache16128

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm126 : Finset ℤ := Finset.Ioc (-129) (-65)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm126

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm126)

def idx (n : ℤ) : ℕ := (n - (-257)).toNat

lemma mem_wMm126 {n : ℤ} (hn : n ∈ wMm126) : (-129) < n ∧ n ≤ (-65) := by
  simpa only [wMm126, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm126) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm126 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm126) :
    2 * Cache16128.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm126 hn
  simp only [idx, Cache16128.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm126) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm126 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm126) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm126 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm126) :
    sampleNumerator (2 * n + 1) =
      (Cache16128.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache16128.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm126) :
    sampleRadius (2 * n + 1) =
      (Cache16128.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache16128.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm126_c_fast : tableEnergyNumerator t wMm126 4 1 = (4395497049428240090655782570883958742675161484810246868491081360694057542113244470940520636064398 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm126 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm126 4 1 =
      ∑ n ∈ wMm126, ((6 * n + 4) ^ 2 - 4) *
        ((Cache16128.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm126_r_fast : tableEnergyRadius t wMm126 4 1 = (360193332664884526832925013045134016458838074422134019535997965558305429739491950571564189 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm126 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm126 4 1 =
      ∑ n ∈ wMm126, (|((6 * n + 4) ^ 2 - 4)| * (Cache16128.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache16128.entries[idx n]?.getD (0, 0)).1| +
          (Cache16128.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm126

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm126_c : tableEnergyNumerator t wMm126 4 1 = (4395497049428240090655782570883958742675161484810246868491081360694057542113244470940520636064398 : ℤ) := by
  exact KsIndex.NegSignProdFastMm126.eMm126_c_fast
theorem eMm126_r : tableEnergyRadius t wMm126 4 1 = (360193332664884526832925013045134016458838074422134019535997965558305429739491950571564189 : ℤ) := by
  exact KsIndex.NegSignProdFastMm126.eMm126_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm126_c
#print axioms KsIndex.NegSignProd.eMm126_r
