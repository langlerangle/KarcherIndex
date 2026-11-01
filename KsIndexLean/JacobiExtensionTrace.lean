module

public import KsIndexLean.JacobiExtensionSeries

@[expose] public section


noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.DtNCircle KsIndex.CircleSobolev

lemma jacobiExtensionH1_trace_coefficient {k : ℕ} (hk : 2 ≤ k)
    (f : Space (1 / 2 : ℝ)) (m : ℤ) :
    circleFourierCoeff (diskTraceCLM (jacobiExtensionH1 hk f)) m =
      if m = 0 then 0 else coeff (1 / 2 : ℝ) f m := by
  classical
  let L := (circleCoefficientCLM m).comp diskTraceCLM
  have ht := L.map_tsum (jacobiExtension_summable hk f)
  have hc (n : NZ) : L (coeff (1 / 2 : ℝ) f n • normalizedJacobiMode hk n) =
      coeff (1 / 2 : ℝ) f n * (Pi.single n.val 1 : ℤ → ℂ) m := by
    simp only [L, ContinuousLinearMap.comp_apply, map_smul,
      normalizedJacobiMode_trace, circleCoefficientCLM_apply, smul_eq_mul]
    rw [congrFun (circleFourierCoeff_congr_ae (fourierTestLp_coe n)) m,
      circleFourierCoeff_fourierAmbient]
  change circleCoefficientCLM m (diskTraceCLM (jacobiExtensionH1 hk f)) =
    ∑' n : NZ, L (coeff (1 / 2 : ℝ) f n • normalizedJacobiMode hk n) at ht
  rw [circleCoefficientCLM_apply] at ht
  rw [ht]
  simp only [hc]
  by_cases hm : m = 0
  · subst m
    have hz (n : NZ) : (Pi.single n.val 1 : ℤ → ℂ) 0 = 0 := by
      simp [Ne.symm n.property]
    simp [hz]
  · rw [ite_eq_right hm, tsum_eq_single (⟨m, hm⟩ : NZ)]
    · simp
    · intro n hn
      have hmn : m ≠ n.val := by
        intro h
        exact hn (Subtype.ext h.symm)
      simp [hmn]

/-- The extension is an exact right inverse of the genuine half-order trace on mean-zero data. -/
lemma jacobiExtensionH1_halfTrace {k : ℕ} (hk : 2 ≤ k) (f : dotted (1 / 2 : ℝ)) :
    halfDiskTraceCLM (jacobiExtensionH1 hk f) = f.val := by
  apply coeff_injective (1 / 2 : ℝ)
  funext m
  change coeff (1 / 2 : ℝ) (halfDiskTrace (jacobiExtensionH1 hk f)) m = _
  rw [coeff_halfDiskTrace, jacobiExtensionH1_trace_coefficient]
  split_ifs with hm
  · subst m
    exact ((mem_dotted _ _).mp f.property).symm
  · rfl

lemma jacobiExtensionH1_diskTrace {k : ℕ} (hk : 2 ≤ k) (f : dotted (1 / 2 : ℝ)) :
    diskTraceCLM (jacobiExtensionH1 hk f) = toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) f.val := by
  have h := congrArg (toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2)) (jacobiExtensionH1_halfTrace hk f)
  simpa only [halfDiskTraceCLM_apply, toL2_halfDiskTrace] using h

end KsIndex.Trace
