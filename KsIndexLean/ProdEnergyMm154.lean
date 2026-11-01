module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache17920

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm154 : Finset ℤ := Finset.Ioc (1663) (1727)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm154

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm154)

def idx (n : ℤ) : ℕ := (n - (1535)).toNat

lemma mem_wMm154 {n : ℤ} (hn : n ∈ wMm154) : (1663) < n ∧ n ≤ (1727) := by
  simpa only [wMm154, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm154) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm154 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm154) :
    2 * Cache17920.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm154 hn
  simp only [idx, Cache17920.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm154) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm154 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm154) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm154 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm154) :
    sampleNumerator (2 * n + 1) =
      (Cache17920.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache17920.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm154) :
    sampleRadius (2 * n + 1) =
      (Cache17920.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache17920.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm154_c_fast : tableEnergyNumerator t wMm154 4 1 = (6393185041073899735568514009973593172800483107952818427895718859699425458683279984240353140328621 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm154 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm154 4 1 =
      ∑ n ∈ wMm154, ((6 * n + 4) ^ 2 - 4) *
        ((Cache17920.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm154_r_fast : tableEnergyRadius t wMm154 4 1 = (21363334323483870524919332820820280136264190989227575295398734121101717459934793566865955 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm154 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm154 4 1 =
      ∑ n ∈ wMm154, (|((6 * n + 4) ^ 2 - 4)| * (Cache17920.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache17920.entries[idx n]?.getD (0, 0)).1| +
          (Cache17920.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm154

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm154_c : tableEnergyNumerator t wMm154 4 1 = (6393185041073899735568514009973593172800483107952818427895718859699425458683279984240353140328621 : ℤ) := by
  exact KsIndex.NegSignProdFastMm154.eMm154_c_fast
theorem eMm154_r : tableEnergyRadius t wMm154 4 1 = (21363334323483870524919332820820280136264190989227575295398734121101717459934793566865955 : ℤ) := by
  exact KsIndex.NegSignProdFastMm154.eMm154_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm154_c
#print axioms KsIndex.NegSignProd.eMm154_r
