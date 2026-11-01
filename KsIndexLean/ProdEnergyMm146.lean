module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache17408

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm146 : Finset ℤ := Finset.Ioc (1151) (1215)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm146

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm146)

def idx (n : ℤ) : ℕ := (n - (1023)).toNat

lemma mem_wMm146 {n : ℤ} (hn : n ∈ wMm146) : (1151) < n ∧ n ≤ (1215) := by
  simpa only [wMm146, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm146) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm146 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm146) :
    2 * Cache17408.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm146 hn
  simp only [idx, Cache17408.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm146) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm146 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm146) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm146 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm146) :
    sampleNumerator (2 * n + 1) =
      (Cache17408.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache17408.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm146) :
    sampleRadius (2 * n + 1) =
      (Cache17408.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache17408.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm146_c_fast : tableEnergyNumerator t wMm146 4 1 = (12976840046090976737827391522307145640960092095454604327977892619105103168977434347641314514994887 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm146 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm146 4 1 =
      ∑ n ∈ wMm146, ((6 * n + 4) ^ 2 - 4) *
        ((Cache17408.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm146_r_fast : tableEnergyRadius t wMm146 4 1 = (44239371147894979832499418026817314793236717265811124534291608193558915188459398309030139 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm146 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm146 4 1 =
      ∑ n ∈ wMm146, (|((6 * n + 4) ^ 2 - 4)| * (Cache17408.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache17408.entries[idx n]?.getD (0, 0)).1| +
          (Cache17408.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm146

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm146_c : tableEnergyNumerator t wMm146 4 1 = (12976840046090976737827391522307145640960092095454604327977892619105103168977434347641314514994887 : ℤ) := by
  exact KsIndex.NegSignProdFastMm146.eMm146_c_fast
theorem eMm146_r : tableEnergyRadius t wMm146 4 1 = (44239371147894979832499418026817314793236717265811124534291608193558915188459398309030139 : ℤ) := by
  exact KsIndex.NegSignProdFastMm146.eMm146_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm146_c
#print axioms KsIndex.NegSignProd.eMm146_r
