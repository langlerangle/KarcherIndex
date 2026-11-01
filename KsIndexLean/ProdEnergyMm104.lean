module

public import KsIndexLean.ProdAccessor
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache14848

@[expose] public section

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wMm104 : Finset ℤ := Finset.Ioc (-1537) (-1473)
end KsIndex.NegSignProd

namespace KsIndex.NegSignProdFastMm104

open KsIndex.AlphaRemarkTrial
open KsIndex.NegSignProd (t wMm104)

def idx (n : ℤ) : ℕ := (n - (-1537)).toNat

lemma mem_wMm104 {n : ℤ} (hn : n ∈ wMm104) : (-1537) < n ∧ n ≤ (-1473) := by
  simpa only [wMm104, Finset.mem_Ioc] using hn

lemma idx_lt {n : ℤ} (hn : n ∈ wMm104) : idx n < 256 := by
  obtain ⟨h1, h2⟩ := mem_wMm104 hn; simp only [idx]; omega

lemma two_mode_idx {n : ℤ} (hn : n ∈ wMm104) :
    2 * Cache14848.mode (idx n) + 1 = 2 * n + 1 := by
  obtain ⟨h1, h2⟩ := mem_wMm104 hn
  simp only [idx, Cache14848.mode]; omega

lemma covLow {n : ℤ} (hn : n ∈ wMm104) : SampleCovered 8196 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm104 hn; exact sampleCovered_of_bound (by omega)

lemma covFast {n : ℤ} (hn : n ∈ wMm104) : SampleCovered 16389 (2 * n + 1) := by
  obtain ⟨h1, h2⟩ := mem_wMm104 hn; exact sampleCovered_of_bound (by omega)

lemma sampleNum_cache {n : ℤ} (hn : n ∈ wMm104) :
    sampleNumerator (2 * n + 1) =
      (Cache14848.entries[idx n]?.getD (0, 0)).1 := by
  have hc := (Cache14848.checked ⟨idx n, idx_lt hn⟩).1
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

lemma sampleRad_cache {n : ℤ} (hn : n ∈ wMm104) :
    sampleRadius (2 * n + 1) =
      (Cache14848.entries[idx n]?.getD (0, 0)).2 := by
  have hc := (Cache14848.checked ⟨idx n, idx_lt hn⟩).2
  rw [two_mode_idx hn] at hc
  have hbridge := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid (covFast hn)
  exact (hc.trans hbridge).symm

theorem eMm104_c_fast : tableEnergyNumerator t wMm104 4 1 = (434622464079428008363185219953092381170573165751628584375536459109352423600212884101736515496741 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid wMm104 4 1 (fun n hn => covLow hn)]
  have h : energyNumerator wMm104 4 1 =
      ∑ n ∈ wMm104, ((6 * n + 4) ^ 2 - 4) *
        ((Cache14848.entries[idx n]?.getD (0, 0)).1) ^ 2 / |6 * n + 4| := by
    unfold energyNumerator
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn]
  rw [h]
  decide +kernel

theorem eMm104_r_fast : tableEnergyRadius t wMm104 4 1 = (6310833864207336059316963227403712123492948913016127222116831164560701768943099188319836 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid wMm104 4 1 (fun n hn => covLow hn)]
  have h : energyRadius wMm104 4 1 =
      ∑ n ∈ wMm104, (|((6 * n + 4) ^ 2 - 4)| * (Cache14848.entries[idx n]?.getD (0, 0)).2 *
        (2 * |(Cache14848.entries[idx n]?.getD (0, 0)).1| +
          (Cache14848.entries[idx n]?.getD (0, 0)).2) / |6 * n + 4| + 2) := by
    unfold energyRadius
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [sampleNum_cache hn, sampleRad_cache hn]
  rw [h]
  decide +kernel

end KsIndex.NegSignProdFastMm104

namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
theorem eMm104_c : tableEnergyNumerator t wMm104 4 1 = (434622464079428008363185219953092381170573165751628584375536459109352423600212884101736515496741 : ℤ) := by
  exact KsIndex.NegSignProdFastMm104.eMm104_c_fast
theorem eMm104_r : tableEnergyRadius t wMm104 4 1 = (6310833864207336059316963227403712123492948913016127222116831164560701768943099188319836 : ℤ) := by
  exact KsIndex.NegSignProdFastMm104.eMm104_r_fast
end KsIndex.NegSignProd
#print axioms KsIndex.NegSignProd.eMm104_c
#print axioms KsIndex.NegSignProd.eMm104_r
