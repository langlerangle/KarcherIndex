module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache16640

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm133 : Finset ℤ := Finset.Ioc (319) (383)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm133

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm133)

def idx (n : ℤ) : ℕ := (n - (255)).toNat

lemma mem_wMm133 {n : ℤ} (hn : n ∈ wMm133) : (319) < n ∧ n ≤ (383) := by
  simpa only [wMm133, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm133) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm133 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm133) :
    2 * Cache16640.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm133 hn
  simp only [idx, Cache16640.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm133) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm133 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm133) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm133 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm133) :
    sampleNumerator (2 * n + 1) =
      (Cache16640.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache16640.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm133) :
    sampleRadius (2 * n + 1) =
      (Cache16640.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache16640.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm133_c_fast : tableEnergyNumerator t wMm133 4 1 = (143571816496657968264598749194002061570290775408641397463501804260924340405459822429710065908965582 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm133 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm133 4 1 =
      ∑ n ∈ wMm133, ((6 * n + 4) ^ 2 - 4) *
        ((Cache16640.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm133_r_fast : tableEnergyRadius t wMm133 4 1 = (523208919946263415850777263904662894142255783539399296732241769291565120625494250774230955 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm133 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm133 4 1 =
      ∑ n ∈ wMm133, (|((6 * n + 4) ^ 2 - 4)| * (Cache16640.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache16640.entries[idx n]?.getD (0, 0)).1| +
          (Cache16640.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm133

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm133_c : tableEnergyNumerator t wMm133 4 1 = (143571816496657968264598749194002061570290775408641397463501804260924340405459822429710065908965582 : ℤ) := by
  exact KsIndex.NegSignProdFastMm133.eMm133_c_fast
theorem eMm133_r : tableEnergyRadius t wMm133 4 1 = (523208919946263415850777263904662894142255783539399296732241769291565120625494250774230955 : ℤ) := by
  exact KsIndex.NegSignProdFastMm133.eMm133_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm133_c
#print axioms KsIndex.NegSignProd.eMm133_r
