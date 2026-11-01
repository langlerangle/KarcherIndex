module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache24320

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm252 : Finset ℤ := Finset.Ioc (7935) (7999)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm252

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm252)

def idx (n : ℤ) : ℕ := (n - (7935)).toNat

lemma mem_wMm252 {n : ℤ} (hn : n ∈ wMm252) : (7935) < n ∧ n ≤ (7999) := by
  simpa only [wMm252, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm252) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm252 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm252) :
    2 * Cache24320.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm252 hn
  simp only [idx, Cache24320.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm252) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm252 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm252) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm252 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm252) :
    sampleNumerator (2 * n + 1) =
      (Cache24320.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache24320.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm252) :
    sampleRadius (2 * n + 1) =
      (Cache24320.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache24320.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm252_c_fast : tableEnergyNumerator t wMm252 4 1 = (307585367967503737195582618440810436034380241123428184239136453178568211933545873074029602882158 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm252 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm252 4 1 =
      ∑ n ∈ wMm252, ((6 * n + 4) ^ 2 - 4) *
        ((Cache24320.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm252_r_fast : tableEnergyRadius t wMm252 4 1 = (941648606850085918879037032130287115062397975135904906840755981793152376657842627802978 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm252 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm252 4 1 =
      ∑ n ∈ wMm252, (|((6 * n + 4) ^ 2 - 4)| * (Cache24320.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache24320.entries[idx n]?.getD (0, 0)).1| +
          (Cache24320.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm252

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm252_c : tableEnergyNumerator t wMm252 4 1 = (307585367967503737195582618440810436034380241123428184239136453178568211933545873074029602882158 : ℤ) := by
  exact KsIndex.NegSignProdFastMm252.eMm252_c_fast
theorem eMm252_r : tableEnergyRadius t wMm252 4 1 = (941648606850085918879037032130287115062397975135904906840755981793152376657842627802978 : ℤ) := by
  exact KsIndex.NegSignProdFastMm252.eMm252_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm252_c
#print axioms KsIndex.NegSignProd.eMm252_r
