module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache15872

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm120 : Finset ℤ := Finset.Ioc (-513) (-449)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm120

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm120)

def idx (n : ℤ) : ℕ := (n - (-513)).toNat

lemma mem_wMm120 {n : ℤ} (hn : n ∈ wMm120) : (-513) < n ∧ n ≤ (-449) := by
  simpa only [wMm120, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm120) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm120 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm120) :
    2 * Cache15872.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm120 hn
  simp only [idx, Cache15872.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm120) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm120 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm120) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm120 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm120) :
    sampleNumerator (2 * n + 1) =
      (Cache15872.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache15872.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm120) :
    sampleRadius (2 * n + 1) =
      (Cache15872.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache15872.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm120_c_fast : tableEnergyNumerator t wMm120 4 1 = (1913372841785421568802946876243055005741334403317414625048066425903411557521148525194946171655295 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm120 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm120 4 1 =
      ∑ n ∈ wMm120, ((6 * n + 4) ^ 2 - 4) *
        ((Cache15872.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm120_r_fast : tableEnergyRadius t wMm120 4 1 = (43584215083889085669317391230329446113358494011284766796800014181922637672340358722879222 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm120 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm120 4 1 =
      ∑ n ∈ wMm120, (|((6 * n + 4) ^ 2 - 4)| * (Cache15872.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache15872.entries[idx n]?.getD (0, 0)).1| +
          (Cache15872.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm120

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm120_c : tableEnergyNumerator t wMm120 4 1 = (1913372841785421568802946876243055005741334403317414625048066425903411557521148525194946171655295 : ℤ) := by
  exact KsIndex.NegSignProdFastMm120.eMm120_c_fast
theorem eMm120_r : tableEnergyRadius t wMm120 4 1 = (43584215083889085669317391230329446113358494011284766796800014181922637672340358722879222 : ℤ) := by
  exact KsIndex.NegSignProdFastMm120.eMm120_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm120_c
#print axioms KsIndex.NegSignProd.eMm120_r
