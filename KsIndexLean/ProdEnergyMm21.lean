module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache9472

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm21 : Finset ℤ := Finset.Ioc (-6849) (-6785)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm21

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm21)

def idx (n : ℤ) : ℕ := (n - (-6913)).toNat

lemma mem_wMm21 {n : ℤ} (hn : n ∈ wMm21) : (-6849) < n ∧ n ≤ (-6785) := by
  simpa only [wMm21, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm21) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm21 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm21) :
    2 * Cache9472.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm21 hn
  simp only [idx, Cache9472.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm21) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm21 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm21) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm21 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm21) :
    sampleNumerator (2 * n + 1) =
      (Cache9472.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache9472.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm21) :
    sampleRadius (2 * n + 1) =
      (Cache9472.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache9472.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm21_c_fast : tableEnergyNumerator t wMm21 4 1 = (44316417332129014306777945857501778142732399124038549587485884380434574232831806068545097352670 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm21 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm21 4 1 =
      ∑ n ∈ wMm21, ((6 * n + 4) ^ 2 - 4) *
        ((Cache9472.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm21_r_fast : tableEnergyRadius t wMm21 4 1 = (420105102446770185079416341836177844072154974124688864892522010616859504217443725662593 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm21 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm21 4 1 =
      ∑ n ∈ wMm21, (|((6 * n + 4) ^ 2 - 4)| * (Cache9472.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache9472.entries[idx n]?.getD (0, 0)).1| +
          (Cache9472.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm21

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm21_c : tableEnergyNumerator t wMm21 4 1 = (44316417332129014306777945857501778142732399124038549587485884380434574232831806068545097352670 : ℤ) := by
  exact KsIndex.NegSignProdFastMm21.eMm21_c_fast
theorem eMm21_r : tableEnergyRadius t wMm21 4 1 = (420105102446770185079416341836177844072154974124688864892522010616859504217443725662593 : ℤ) := by
  exact KsIndex.NegSignProdFastMm21.eMm21_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm21_c
#print axioms KsIndex.NegSignProd.eMm21_r
