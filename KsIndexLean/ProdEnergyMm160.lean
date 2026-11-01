module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache18432

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm160 : Finset ℤ := Finset.Ioc (2047) (2111)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm160

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm160)

def idx (n : ℤ) : ℕ := (n - (2047)).toNat

lemma mem_wMm160 {n : ℤ} (hn : n ∈ wMm160) : (2047) < n ∧ n ≤ (2111) := by
  simpa only [wMm160, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm160) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm160 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm160) :
    2 * Cache18432.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm160 hn
  simp only [idx, Cache18432.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm160) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm160 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm160) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm160 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm160) :
    sampleNumerator (2 * n + 1) =
      (Cache18432.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache18432.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm160) :
    sampleRadius (2 * n + 1) =
      (Cache18432.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache18432.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm160_c_fast : tableEnergyNumerator t wMm160 4 1 = (4279161680348675005954718687461487052417897892769321070920103877710279048252271017163744169219537 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm160 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm160 4 1 =
      ∑ n ∈ wMm160, ((6 * n + 4) ^ 2 - 4) *
        ((Cache18432.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm160_r_fast : tableEnergyRadius t wMm160 4 1 = (14136760341921568553088866629165824456352521876817332721737445402128957925103406917758680 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm160 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm160 4 1 =
      ∑ n ∈ wMm160, (|((6 * n + 4) ^ 2 - 4)| * (Cache18432.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache18432.entries[idx n]?.getD (0, 0)).1| +
          (Cache18432.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm160

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm160_c : tableEnergyNumerator t wMm160 4 1 = (4279161680348675005954718687461487052417897892769321070920103877710279048252271017163744169219537 : ℤ) := by
  exact KsIndex.NegSignProdFastMm160.eMm160_c_fast
theorem eMm160_r : tableEnergyRadius t wMm160 4 1 = (14136760341921568553088866629165824456352521876817332721737445402128957925103406917758680 : ℤ) := by
  exact KsIndex.NegSignProdFastMm160.eMm160_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm160_c
#print axioms KsIndex.NegSignProd.eMm160_r
