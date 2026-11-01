module

/-
KsIndexLean — ZeroMeanTrace: the boundary trace of the angular average
([ksindexi] tex 1838–1841: "the trace map preserves each such Fourier class",
specialized to the zero-mean class).

The trace of `P₀ u` is the constant Fourier component of the trace of `u`:
coefficientwise, `c_m(trace (P₀ u)) = δ_{m0} · c₀(trace u)`.  Hence members
of `ker P₀` have mean-zero trace, and their half-order traces lie in the
paper's dotted (mean-zero) `Ḣ^{1/2}`. These trace identities support the
`nop-sphop` zero-mean block argument.
-/
public import KsIndexLean.ZeroMeanProjection
public import KsIndexLean.FourierRadialFTC
public import KsIndexLean.CircleFourierRotation
public import KsIndexLean.HalfOrderDiskTrace

@[expose] public section


noncomputable section
open Set MeasureTheory intervalIntegral
namespace KsIndex.Trace
open KsIndex.WeakH1

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

lemma intervalIntegrable_boundaryRotation_trace (u : ComplexH1) :
    IntervalIntegrable (fun θ => boundaryRotation θ (diskTraceCLM u))
      volume 0 (2 * Real.pi) := by
  have he : (fun θ => boundaryRotation θ (diskTraceCLM u)) =
      fun θ => diskTraceCLM (diskRotation θ u) := by
    funext θ
    exact (diskTrace_rotation θ u).symm
  rw [he]
  exact (diskTraceCLM.continuous.comp (continuous_diskRotation u)).intervalIntegrable 0
    (2 * Real.pi)

/-- The trace of the angular average is the boundary average of the trace. -/
lemma diskTrace_angularAverage (u : ComplexH1) :
    diskTraceCLM (angularAverage u) =
      (2 * Real.pi)⁻¹ • ∫ θ in (0:ℝ)..(2 * Real.pi),
        boundaryRotation θ (diskTraceCLM u) := by
  unfold angularAverage
  rw [ContinuousLinearMap.map_smul_of_tower]
  congr 1
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm _
    (intervalIntegrable_diskRotation u 0 (2 * Real.pi))]
  apply integral_congr
  intro θ _
  exact diskTrace_rotation θ u

/-- Coefficientwise, averaging retains exactly the constant component. -/
lemma circleCoefficient_trace_angularAverage (m : ℤ) (u : ComplexH1) :
    circleCoefficientCLM m (diskTraceCLM (angularAverage u)) =
      if m = 0 then circleCoefficientCLM 0 (diskTraceCLM u) else 0 := by
  rw [diskTrace_angularAverage, ContinuousLinearMap.map_smul_of_tower]
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm _
    (intervalIntegrable_boundaryRotation_trace u)]
  have hcongr : (fun θ => circleCoefficientCLM m (boundaryRotation θ (diskTraceCLM u))) =
      fun θ : ℝ => (fourier m ((θ : ℝ) : AddCircle (2 * Real.pi)) : ℂ) *
        circleCoefficientCLM m (diskTraceCLM u) := by
    funext θ
    exact circleFourierCLE_boundaryRotation θ (diskTraceCLM u) m
  rw [hcongr, intervalIntegral.integral_mul_const]
  have h2pi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt Real.two_pi_pos)
  have hexp : ∀ θ : ℝ, (fourier m ((θ : ℝ) : AddCircle (2 * Real.pi)) : ℂ) =
      Complex.exp ((m : ℂ) * Complex.I * θ) := by
    intro θ
    rw [fourier_coe_apply]
    congr 1
    push_cast
    field_simp
  have hfour : (∫ θ in (0:ℝ)..(2 * Real.pi),
      (fourier m ((θ : ℝ) : AddCircle (2 * Real.pi)) : ℂ)) =
      if m = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
    simp_rw [hexp]
    by_cases hm : m = 0
    · subst hm
      simp only [reduceIte]
      simp only [Int.cast_zero, zero_mul, Complex.exp_zero]
      rw [intervalIntegral.integral_const, sub_zero]
      simp [Complex.real_smul]
    · simp only [hm, ite_false]
      have hc : (m : ℂ) * Complex.I ≠ 0 := by
        apply mul_ne_zero _ Complex.I_ne_zero
        exact_mod_cast hm
      rw [integral_exp_mul_complex hc]
      have hone : Complex.exp ((m : ℂ) * Complex.I * (2 * Real.pi)) = 1 := by
        rw [show (m : ℂ) * Complex.I * (2 * Real.pi) =
          (m : ℤ) * (2 * Real.pi * Complex.I) by ring]
        exact Complex.exp_int_mul_two_pi_mul_I m
      simp [hone]
  rw [hfour]
  by_cases hm : m = 0
  · subst hm
    simp only [reduceIte]
    rw [← smul_mul_assoc]
    have h2 : (2 * Real.pi : ℝ)⁻¹ • ((2 * Real.pi : ℝ) : ℂ) = 1 := by
      rw [Complex.real_smul, ← Complex.ofReal_mul,
        inv_mul_cancel₀ (ne_of_gt Real.two_pi_pos), Complex.ofReal_one]
    rw [h2, one_mul]
  · simp only [hm, ite_false, zero_mul, smul_zero]

/-- A member of `ker P₀` has mean-zero boundary trace. -/
lemma circleCoefficient_zero_of_angularAverage_eq_zero {u : ComplexH1}
    (hu : angularAverage u = 0) :
    circleCoefficientCLM 0 (diskTraceCLM u) = 0 := by
  have h := circleCoefficient_trace_angularAverage 0 u
  rw [hu] at h
  simp only [map_zero, ite_true] at h
  exact h.symm

/-- The half-order trace of a `ker P₀` member lies in the paper's mean-zero
`Ḣ^{1/2}` — the domain of the normalized Jacobi extension. -/
lemma halfDiskTrace_mem_dotted_of_angularAverage_eq_zero {u : ComplexH1}
    (hu : angularAverage u = 0) :
    halfDiskTraceCLM u ∈ KsIndex.CircleSobolev.dotted (1 / 2 : ℝ) := by
  rw [KsIndex.CircleSobolev.mem_dotted]
  have hc := circleCoefficient_zero_of_angularAverage_eq_zero hu
  have ht' := DFunLike.congr_fun toL2_comp_halfDiskTraceCLM u
  have ht : KsIndex.CircleSobolev.toL2 (show (0:ℝ) ≤ 1 / 2 by norm_num)
      (halfDiskTraceCLM u) = diskTraceCLM u := ht'
  have hcoeff := KsIndex.CircleSobolev.fourierCoeff_toL2
    (show (0:ℝ) ≤ 1 / 2 by norm_num) (halfDiskTraceCLM u) 0
  rw [← hcoeff]
  simp only [circleCoefficientCLM_apply] at hc
  rw [show KsIndex.CircleSobolev.toL2 (show (0:ℝ) ≤ 1 / 2 by norm_num) (halfDiskTraceCLM u) =
    diskTraceCLM u from ht]
  exact hc

end KsIndex.Trace
