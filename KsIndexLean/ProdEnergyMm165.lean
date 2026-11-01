module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache18688

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm165 : Finset ℤ := Finset.Ioc (2367) (2431)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm165

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm165)

def idx (n : ℤ) : ℕ := (n - (2303)).toNat

lemma mem_wMm165 {n : ℤ} (hn : n ∈ wMm165) : (2367) < n ∧ n ≤ (2431) := by
  simpa only [wMm165, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm165) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm165 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm165) :
    2 * Cache18688.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm165 hn
  simp only [idx, Cache18688.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm165) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm165 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm165) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm165 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm165) :
    sampleNumerator (2 * n + 1) =
      (Cache18688.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache18688.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm165) :
    sampleRadius (2 * n + 1) =
      (Cache18688.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache18688.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm165_c_fast : tableEnergyNumerator t wMm165 4 1 = (3230044732721571793835703230349570650739040385020301597038637652945686312056578773534583031634029 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm165 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm165 4 1 =
      ∑ n ∈ wMm165, ((6 * n + 4) ^ 2 - 4) *
        ((Cache18688.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm165_r_fast : tableEnergyRadius t wMm165 4 1 = (10585478394004407820664665037052963616176087984147725908891358620389784514052055920561602 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm165 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm165 4 1 =
      ∑ n ∈ wMm165, (|((6 * n + 4) ^ 2 - 4)| * (Cache18688.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache18688.entries[idx n]?.getD (0, 0)).1| +
          (Cache18688.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm165

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm165_c : tableEnergyNumerator t wMm165 4 1 = (3230044732721571793835703230349570650739040385020301597038637652945686312056578773534583031634029 : ℤ) := by
  exact KsIndex.NegSignProdFastMm165.eMm165_c_fast
theorem eMm165_r : tableEnergyRadius t wMm165 4 1 = (10585478394004407820664665037052963616176087984147725908891358620389784514052055920561602 : ℤ) := by
  exact KsIndex.NegSignProdFastMm165.eMm165_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm165_c
#print axioms KsIndex.NegSignProd.eMm165_r
