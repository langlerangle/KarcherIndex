module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache20224

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm188 : Finset ℤ := Finset.Ioc (3839) (3903)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm188

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm188)

def idx (n : ℤ) : ℕ := (n - (3839)).toNat

lemma mem_wMm188 {n : ℤ} (hn : n ∈ wMm188) : (3839) < n ∧ n ≤ (3903) := by
  simpa only [wMm188, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm188) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm188 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm188) :
    2 * Cache20224.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm188 hn
  simp only [idx, Cache20224.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm188) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm188 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm188) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm188 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm188) :
    sampleNumerator (2 * n + 1) =
      (Cache20224.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache20224.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm188) :
    sampleRadius (2 * n + 1) =
      (Cache20224.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache20224.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm188_c_fast : tableEnergyNumerator t wMm188 4 1 = (1263301743017680803912074312681607742051817748656403520586592390277816882220534107877066746972551 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm188 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm188 4 1 =
      ∑ n ∈ wMm188, ((6 * n + 4) ^ 2 - 4) *
        ((Cache20224.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm188_r_fast : tableEnergyRadius t wMm188 4 1 = (4029797414063685476114497193838680236198880036750646774282389153809916958660748706552794 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm188 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm188 4 1 =
      ∑ n ∈ wMm188, (|((6 * n + 4) ^ 2 - 4)| * (Cache20224.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache20224.entries[idx n]?.getD (0, 0)).1| +
          (Cache20224.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm188

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm188_c : tableEnergyNumerator t wMm188 4 1 = (1263301743017680803912074312681607742051817748656403520586592390277816882220534107877066746972551 : ℤ) := by
  exact KsIndex.NegSignProdFastMm188.eMm188_c_fast
theorem eMm188_r : tableEnergyRadius t wMm188 4 1 = (4029797414063685476114497193838680236198880036750646774282389153809916958660748706552794 : ℤ) := by
  exact KsIndex.NegSignProdFastMm188.eMm188_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm188_c
#print axioms KsIndex.NegSignProd.eMm188_r
