module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache15872

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm122 : Finset ℤ := Finset.Ioc (-385) (-321)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm122

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm122)

def idx (n : ℤ) : ℕ := (n - (-513)).toNat

lemma mem_wMm122 {n : ℤ} (hn : n ∈ wMm122) : (-385) < n ∧ n ≤ (-321) := by
  simpa only [wMm122, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm122) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm122 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm122) :
    2 * Cache15872.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm122 hn
  simp only [idx, Cache15872.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm122) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm122 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm122) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm122 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm122) :
    sampleNumerator (2 * n + 1) =
      (Cache15872.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache15872.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm122) :
    sampleRadius (2 * n + 1) =
      (Cache15872.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache15872.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm122_c_fast : tableEnergyNumerator t wMm122 4 1 = (2676070548246069254026361855864258096866171210317774426629236768663122225639554512518554530345720 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm122 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm122 4 1 =
      ∑ n ∈ wMm122, ((6 * n + 4) ^ 2 - 4) *
        ((Cache15872.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm122_r_fast : tableEnergyRadius t wMm122 4 1 = (71368939243722580761690355021894432697586927075089287986780801852320261916378807361511631 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm122 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm122 4 1 =
      ∑ n ∈ wMm122, (|((6 * n + 4) ^ 2 - 4)| * (Cache15872.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache15872.entries[idx n]?.getD (0, 0)).1| +
          (Cache15872.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm122

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm122_c : tableEnergyNumerator t wMm122 4 1 = (2676070548246069254026361855864258096866171210317774426629236768663122225639554512518554530345720 : ℤ) := by
  exact KsIndex.NegSignProdFastMm122.eMm122_c_fast
theorem eMm122_r : tableEnergyRadius t wMm122 4 1 = (71368939243722580761690355021894432697586927075089287986780801852320261916378807361511631 : ℤ) := by
  exact KsIndex.NegSignProdFastMm122.eMm122_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm122_c
#print axioms KsIndex.NegSignProd.eMm122_r
