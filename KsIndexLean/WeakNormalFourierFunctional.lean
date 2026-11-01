module

public import KsIndexLean.WeakBoundaryResidual
public import KsIndexLean.CharacterEigenTestExtension
public import KsIndexLean.FiniteFourierReconstruction

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical KsIndex.Spectral
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The conjugate boundary residual is linear in the solution. No normal-trace
regularity is assumed in this definition. -/
def weakNormalFourierFunctional (k : ℕ) (lam : ℝ) (n : ℤ) : ComplexH1 →ₗ[ℂ] ℂ :=
  { toFun := fun u => weakJacobi (sphericalEigenPotential (surfacePotential k) lam)
      (globalSmoothH1 (fourierAmbient n) (contDiff_fourierAmbient n)) u
    map_add' := weakJacobi_add_right _ _
    map_smul' := fun c u => weakJacobi_smul_right _ c _ u }

lemma weakNormalFourierFunctional_eq (k : ℕ) (lam : ℝ) (u : ComplexH1) (n : ℤ)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v)) :
    weakNormalFourierFunctional k lam n u =
      ((2 * Real.pi : ℝ) : ℂ) * eigenDiskNormalMode k lam u n := by
  have h := congrArg (starRingEnd ℂ) (sphericalEigen_fourier_extension_flux_pairing k lam u n hu)
  simpa only [map_mul, Complex.conj_ofReal, starRingEnd_self_apply, weakJacobi_conj,
    weakNormalFourierFunctional, LinearMap.coe_mk, AddHom.coe_mk] using h

lemma smoothFourier_trace_eq (n : ℤ) :
    diskTraceCLM (globalSmoothH1 (fourierAmbient n) (contDiff_fourierAmbient n)) =
      ContinuousMap.toLp 2 circleMeasure ℂ (circleFourierModeContinuous n) := by
  apply Lp.ext
  exact (globalSmoothH1_trace _ _).trans
    (ContinuousMap.coeFn_toLp circleMeasure (circleFourierModeContinuous n)).symm

lemma smoothFourier_trace_rotation (θ : ℝ) (n : ℤ) :
    diskTraceCLM (diskRotation θ
      (globalSmoothH1 (fourierAmbient n) (contDiff_fourierAmbient n))) =
    diskTraceCLM (fourier n (θ : AddCircle (2 * Real.pi)) •
      globalSmoothH1 (fourierAmbient n) (contDiff_fourierAmbient n)) := by
  rw [diskTrace_rotation, map_smul, smoothFourier_trace_eq]
  apply circleFourierCLE.injective
  apply Subtype.ext
  funext m
  rw [circleFourierCLE_boundaryRotation, map_smul]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, circleFourierCLE_apply,
    ← circleCoefficientCLM_apply, circleFourierMode_coefficient]
  split_ifs with h
  · subst m; rfl
  · simp

lemma weakNormalFourierFunctional_rotation (k : ℕ) (lam θ : ℝ) (u : ComplexH1)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v)) (n : ℤ) :
    weakNormalFourierFunctional k lam n (diskRotation θ u) =
      fourier n (θ : AddCircle (2 * Real.pi)) * weakNormalFourierFunctional k lam n u := by
  let t := globalSmoothH1 (fourierAmbient n) (contDiff_fourierAmbient n)
  let V := sphericalEigenPotential (surfacePotential k) lam
  have he : diskRotation θ (diskRotation (-θ) t) = t := by
    rw [← diskRotation_add, add_neg_cancel, diskRotation_zero]
  have hr := sphericalEigenJacobi_diskRotation k lam θ (diskRotation (-θ) t) u
  rw [he] at hr
  have ht := weakJacobi_eq_of_trace_eq V u
    (fun v hv => (spherical_eigen_equation_iff _ lam u v).mp (hu v hv))
    (diskRotation (-θ) t) (fourier n ((-θ : ℝ) : AddCircle (2 * Real.pi)) • t)
    (smoothFourier_trace_rotation (-θ) n)
  rw [weakJacobi_smul_right] at ht
  have ht' := congrArg (starRingEnd ℂ) ht
  simp only [weakJacobi_conj, map_mul] at ht'
  change weakJacobi V t (diskRotation θ u) = _
  rw [hr, ht']
  have hc : (starRingEnd ℂ) (fourier n ((-θ : ℝ) : AddCircle (2 * Real.pi))) =
      fourier n (θ : AddCircle (2 * Real.pi)) := by
    simp only [fourier_apply, smul_neg, AddCircle.coe_neg,
      AddCircle.toCircle_neg, Circle.coe_inv_eq_conj, starRingEnd_self_apply]
  rw [hc]
  rfl

end KsIndex.Trace
