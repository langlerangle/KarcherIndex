module

public import KsIndexLean.DiskRotationContinuity
public import KsIndexLean.NormalPolynomialWeakPairing

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

lemma map_fourierCoeffOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (L : E →L[ℂ] F) (f : ℝ → E) (hf : Continuous f) (n : ℤ) :
    L (fourierCoeffOn Real.two_pi_pos f n) = fourierCoeffOn Real.two_pi_pos (fun θ => L (f θ)) n := by
  have hi : IntervalIntegrable (fun θ : ℝ =>
      fourier (-n) (θ : AddCircle (2 * Real.pi)) • f θ) volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    exact ((fourier (-n)).continuous.comp continuous_quotient_mk').smul hf
  simp only [fourierCoeffOn_eq_integral]
  simp_rw [sub_zero]
  rw [L.map_smul_of_tower]
  congr 1
  simpa only [map_smul, fourier_coe_apply, sub_zero] using (L.intervalIntegral_comp_comm hi).symm

/-- Angular projection formed inside the full weak H1 carrier. -/
def diskAngularProjection (n : ℤ) (u : ComplexH1) : ComplexH1 :=
  fourierCoeffOn Real.two_pi_pos (fun θ => diskRotation θ u) n

lemma diskAngularProjection_map (L : ComplexH1 →L[ℂ] ℂ) (n : ℤ) (u : ComplexH1) :
    L (diskAngularProjection n u) =
      fourierCoeffOn Real.two_pi_pos (fun θ => L (diskRotation θ u)) n :=
  map_fourierCoeffOn L _ (continuous_diskRotation u) n

lemma fourierCoeffOn_fourier (n m : ℤ) :
    fourierCoeffOn Real.two_pi_pos (fun θ : ℝ => fourier m (θ : AddCircle (2 * Real.pi))) n =
      if n = m then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 2 * Real.pi) m) n
  rw [fourierCoeff_eq_intervalIntegral _ _ 0] at h
  rw [fourierCoeffOn_eq_integral]
  simp_rw [sub_zero]
  simpa only [fourier_coe_apply, sub_zero, zero_add, Pi.single_apply, eq_comm] using h

lemma diskAngularProjection_trace_coefficient (n m : ℤ) (u : ComplexH1) :
    circleCoefficientCLM m (diskTraceCLM (diskAngularProjection n u)) =
      if m = n then circleCoefficientCLM m (diskTraceCLM u) else 0 := by
  rw [show circleCoefficientCLM m (diskTraceCLM (diskAngularProjection n u)) =
    ((circleCoefficientCLM m).comp diskTraceCLM) (diskAngularProjection n u) from rfl,
    diskAngularProjection_map]
  have he (θ : ℝ) : ((circleCoefficientCLM m).comp diskTraceCLM) (diskRotation θ u) =
      circleCoefficientCLM m (diskTraceCLM u) * fourier m (θ : AddCircle (2 * Real.pi)) := by
    simp only [ContinuousLinearMap.comp_apply, diskTrace_rotation, circleCoefficientCLM_apply]
    simpa only [circleFourierCLE_apply, mul_comm] using circleFourierCLE_boundaryRotation θ (diskTraceCLM u) m
  simp_rw [he]
  rw [fourierCoeffOn.const_mul, fourierCoeffOn_fourier]
  by_cases h : m = n
  · subst m; simp
  · simp only [Ne.symm h, h, ite_false, mul_zero]

lemma diskAngularProjection_mem_finiteFourierTraceTests (n : ℤ) (u : ComplexH1) :
    diskAngularProjection n u ∈ finiteFourierTraceTests := by
  refine ⟨{n}, fun m => circleCoefficientCLM m (diskTraceCLM u), ?_⟩
  apply circleFourierCLE.injective
  apply Subtype.ext
  funext m
  simp only [circleFourierCLE_apply, ← circleCoefficientCLM_apply,
    diskAngularProjection_trace_coefficient, circleFourierPolynomial_coefficient,
    Finset.mem_singleton]

end KsIndex.Trace
