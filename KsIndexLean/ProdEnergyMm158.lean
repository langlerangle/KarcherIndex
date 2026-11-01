module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache18176

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm158 : Finset ℤ := Finset.Ioc (1919) (1983)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm158

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm158)

def idx (n : ℤ) : ℕ := (n - (1791)).toNat

lemma mem_wMm158 {n : ℤ} (hn : n ∈ wMm158) : (1919) < n ∧ n ≤ (1983) := by
  simpa only [wMm158, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm158) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm158 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm158) :
    2 * Cache18176.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm158 hn
  simp only [idx, Cache18176.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm158) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm158 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm158) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm158 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm158) :
    sampleNumerator (2 * n + 1) =
      (Cache18176.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache18176.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm158) :
    sampleRadius (2 * n + 1) =
      (Cache18176.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache18176.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm158_c_fast : tableEnergyNumerator t wMm158 4 1 = (4848414861289445819073614557581961838437743420098156750831250586136410116244281435242710982158799 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm158 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm158 4 1 =
      ∑ n ∈ wMm158, ((6 * n + 4) ^ 2 - 4) *
        ((Cache18176.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm158_r_fast : tableEnergyRadius t wMm158 4 1 = (16074471374363233683480435405659183830040429447206681786069578402990596008708771140750317 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm158 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm158 4 1 =
      ∑ n ∈ wMm158, (|((6 * n + 4) ^ 2 - 4)| * (Cache18176.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache18176.entries[idx n]?.getD (0, 0)).1| +
          (Cache18176.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm158

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm158_c : tableEnergyNumerator t wMm158 4 1 = (4848414861289445819073614557581961838437743420098156750831250586136410116244281435242710982158799 : ℤ) := by
  exact KsIndex.NegSignProdFastMm158.eMm158_c_fast
theorem eMm158_r : tableEnergyRadius t wMm158 4 1 = (16074471374363233683480435405659183830040429447206681786069578402990596008708771140750317 : ℤ) := by
  exact KsIndex.NegSignProdFastMm158.eMm158_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm158_c
#print axioms KsIndex.NegSignProd.eMm158_r
