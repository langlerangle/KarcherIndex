module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache12544

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm70 : Finset ℤ := Finset.Ioc (-3713) (-3649)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm70

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm70)

def idx (n : ℤ) : ℕ := (n - (-3841)).toNat

lemma mem_wMm70 {n : ℤ} (hn : n ∈ wMm70) : (-3713) < n ∧ n ≤ (-3649) := by
  simpa only [wMm70, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm70) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm70 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm70) :
    2 * Cache12544.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm70 hn
  simp only [idx, Cache12544.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm70) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm70 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm70) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm70 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm70) :
    sampleNumerator (2 * n + 1) =
      (Cache12544.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache12544.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm70) :
    sampleRadius (2 * n + 1) =
      (Cache12544.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache12544.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm70_c_fast : tableEnergyNumerator t wMm70 4 1 = (115834520065666653506412795634565091827652655011357571727044448956903782218643789745285491731689 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm70 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm70 4 1 =
      ∑ n ∈ wMm70, ((6 * n + 4) ^ 2 - 4) *
        ((Cache12544.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm70_r_fast : tableEnergyRadius t wMm70 4 1 = (1286278456898903612063078814241077531357693491619590163763338580111886673423089187951737 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm70 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm70 4 1 =
      ∑ n ∈ wMm70, (|((6 * n + 4) ^ 2 - 4)| * (Cache12544.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache12544.entries[idx n]?.getD (0, 0)).1| +
          (Cache12544.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm70

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm70_c : tableEnergyNumerator t wMm70 4 1 = (115834520065666653506412795634565091827652655011357571727044448956903782218643789745285491731689 : ℤ) := by
  exact KsIndex.NegSignProdFastMm70.eMm70_c_fast
theorem eMm70_r : tableEnergyRadius t wMm70 4 1 = (1286278456898903612063078814241077531357693491619590163763338580111886673423089187951737 : ℤ) := by
  exact KsIndex.NegSignProdFastMm70.eMm70_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm70_c
#print axioms KsIndex.NegSignProd.eMm70_r
