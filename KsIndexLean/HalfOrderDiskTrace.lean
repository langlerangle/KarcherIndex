module

public import KsIndexLean.CollarTraceEnergy
public import KsIndexLean.CircleSobolevCompact

@[expose] public section


/-! The bounded half-order trace, agreeing with the existing weak disk trace. -/
noncomputable section
open MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.CircleSobolev

/-- The unique half-order representative of the existing L2-valued trace. -/
def halfDiskTrace (u : ComplexH1) : Space (1 / 2 : ℝ) :=
  (diskTrace_exists_unique_half u).exists.choose

@[simp] theorem toL2_halfDiskTrace (u : ComplexH1) :
    toL2 (show (0 : ℝ) ≤ 1 / 2 by norm_num) (halfDiskTrace u) = diskTraceCLM u :=
  (diskTrace_exists_unique_half u).exists.choose_spec

@[simp] theorem coeff_halfDiskTrace (u : ComplexH1) (n : ℤ) :
    coeff (1 / 2 : ℝ) (halfDiskTrace u) n = circleFourierCoeff (diskTraceCLM u) n := by
  rw [← fourierCoeff_toL2 (show (0 : ℝ) ≤ 1 / 2 by norm_num), toL2_halfDiskTrace]

theorem halfDiskTrace_add (u v : ComplexH1) : halfDiskTrace (u + v) = halfDiskTrace u + halfDiskTrace v := by
  apply toL2_injective (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rw [map_add, toL2_halfDiskTrace, toL2_halfDiskTrace, toL2_halfDiskTrace, map_add]

theorem halfDiskTrace_smul (c : ℂ) (u : ComplexH1) : halfDiskTrace (c • u) = c • halfDiskTrace u := by
  apply toL2_injective (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rw [map_smul, toL2_halfDiskTrace, toL2_halfDiskTrace, map_smul]

theorem halfDiskTrace_norm_sq_le (u : ComplexH1) :
    ‖halfDiskTrace u‖ ^ 2 ≤ (36 * (2 * Real.pi)⁻¹) * ‖u‖ ^ 2 := by
  have h := (hasSum_weighted_sq (1 / 2 : ℝ) (halfDiskTrace u)).tsum_eq
  simp only [weight_sq, coeff_halfDiskTrace,
    show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one] at h
  rw [← h]
  exact diskTrace_half_weight_tsum_le u

theorem halfDiskTrace_norm_le (u : ComplexH1) :
    ‖halfDiskTrace u‖ ≤ Real.sqrt (36 * (2 * Real.pi)⁻¹) * ‖u‖ := by
  have h := halfDiskTrace_norm_sq_le u
  have hs := Real.sq_sqrt (show 0 ≤ 36 * (2 * Real.pi)⁻¹ by positivity)
  have hp : 0 ≤ Real.sqrt (36 * (2 * Real.pi)⁻¹) * ‖u‖ := by positivity
  nlinarith [sq_nonneg (‖halfDiskTrace u‖ - Real.sqrt (36 * (2 * Real.pi)⁻¹) * ‖u‖)]

/-- Bounded complex-linear H1(disk) -> H^(1/2)(circle) trace. -/
def halfDiskTraceCLM : ComplexH1 →L[ℂ] Space (1 / 2 : ℝ) :=
  LinearMap.mkContinuous
    { toFun := halfDiskTrace
      map_add' := halfDiskTrace_add
      map_smul' := halfDiskTrace_smul }
    (Real.sqrt (36 * (2 * Real.pi)⁻¹)) halfDiskTrace_norm_le

@[simp] theorem halfDiskTraceCLM_apply (u : ComplexH1) : halfDiskTraceCLM u = halfDiskTrace u := rfl

/-- Exact agreement as operators, on the same geometric circle and measure. -/
theorem toL2_comp_halfDiskTraceCLM :
    (toL2 (show (0 : ℝ) ≤ 1 / 2 by norm_num)).comp halfDiskTraceCLM = diskTraceCLM := by
  apply ContinuousLinearMap.ext
  intro u
  exact toL2_halfDiskTrace u

theorem norm_halfDiskTraceCLM_le : ‖halfDiskTraceCLM‖ ≤ Real.sqrt (36 * (2 * Real.pi)⁻¹) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) halfDiskTrace_norm_le

/-- Compactness of the L²-valued trace follows from its half-order factorization. -/
theorem isCompactOperator_diskTraceCLM : IsCompactOperator diskTraceCLM := by
  rw [← toL2_comp_halfDiskTraceCLM]
  exact isCompactOperator_toL2_half.comp_clm halfDiskTraceCLM

end KsIndex.Trace
