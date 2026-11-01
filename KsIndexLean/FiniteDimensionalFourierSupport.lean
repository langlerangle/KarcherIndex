module

public import KsIndexLean.CircleFourierRotation
public import KsIndexLean.FourierRadialFTC
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace

/-- A finite-dimensional invariant space admits only finitely many nonzero
coefficient functionals with distinct rotation eigenvalues. -/
theorem finite_nonzero_eigenfunctionals {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] {ι : Type*} (T : E →ₗ[ℂ] E)
    (l : ι → E →ₗ[ℂ] ℂ) (v : ι → ℂ) (hv : Function.Injective v)
    (hl : ∀ i x, l i (T x) = v i * l i x) :
    {i | l i ≠ 0}.Finite := by
  have hsub : {i | l i ≠ 0} ⊆ v ⁻¹' {z | Module.End.HasEigenvalue T.dualMap z} := by
    intro i hi
    apply Module.End.hasEigenvalue_of_hasEigenvector
    apply Module.End.hasEigenvector_iff.mpr
    refine ⟨?_, hi⟩
    apply Module.End.mem_eigenspace_iff.mpr
    ext x
    exact hl i x
  exact ((Module.End.finite_hasEigenvalue T.dualMap).preimage hv.injOn).subset hsub

/-- Finite angular support, uniformly on any finite-dimensional circle space
invariant under a rotation whose Fourier characters are pairwise distinct. -/
theorem finite_fourier_support_of_invariant_finiteDimensional
    (W : Submodule ℂ (Lp ℂ 2 circleMeasure)) [FiniteDimensional ℂ W]
    (θ : ℝ) (hv : Function.Injective (fun n : ℤ => fourier n (θ : AddCircle (2 * Real.pi))))
    (hW : ∀ f ∈ W, boundaryRotation θ f ∈ W) :
    {n : ℤ | ∃ f ∈ W, circleFourierCoeff f n ≠ 0}.Finite := by
  let T : W →ₗ[ℂ] W :=
    { toFun := fun f => ⟨boundaryRotation θ f, hW f f.property⟩
      map_add' := by intro f g; apply Subtype.ext; exact map_add (boundaryRotation θ) (f : Lp ℂ 2 circleMeasure) (g : Lp ℂ 2 circleMeasure)
      map_smul' := by intro c f; apply Subtype.ext; exact map_smul (boundaryRotation θ) c (f : Lp ℂ 2 circleMeasure) }
  let l : ℤ → W →ₗ[ℂ] ℂ := fun n => (circleCoefficientCLM n).toLinearMap.comp W.subtype
  have hl (n : ℤ) (f : W) : l n (T f) =
      fourier n (θ : AddCircle (2 * Real.pi)) * l n f := by
    change circleCoefficientCLM n (boundaryRotation θ f) =
      fourier n (θ : AddCircle (2 * Real.pi)) * circleCoefficientCLM n f
    simpa only [circleCoefficientCLM_apply, circleFourierCLE_apply] using
      circleFourierCLE_boundaryRotation θ f n
  apply (finite_nonzero_eigenfunctionals T l _ hv hl).subset
  rintro n ⟨f, hf, hn⟩ he
  apply hn
  have h := congrArg (fun L : W →ₗ[ℂ] ℂ => L ⟨f, hf⟩) he
  simpa only [l, LinearMap.comp_apply, Submodule.subtype_apply,
    ContinuousLinearMap.coe_coe, circleCoefficientCLM_apply, LinearMap.zero_apply] using h

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

lemma fourier_injective_of_irrational_rotation (θ : ℝ)
    (hθ : Irrational (θ / (2 * Real.pi))) :
    Function.Injective (fun n : ℤ => fourier n (θ : AddCircle (2 * Real.pi))) := by
  have hi : ¬ IsOfFinAddOrder (θ : AddCircle (2 * Real.pi)) := by
    simpa only [AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div, Irrational, Set.mem_range] using hθ
  intro n m h
  apply (injective_zsmul_iff_not_isOfFinAddOrder.mpr hi)
  apply AddCircle.injective_toCircle Real.two_pi_pos.ne'
  apply Subtype.ext
  exact h

/-- Irrational rotation supplies the distinct-character hypothesis concretely. -/
theorem finite_fourier_support_of_irrational_invariance
    (W : Submodule ℂ (Lp ℂ 2 circleMeasure)) [FiniteDimensional ℂ W]
    (θ : ℝ) (hθ : Irrational (θ / (2 * Real.pi)))
    (hW : ∀ f ∈ W, boundaryRotation θ f ∈ W) :
    {n : ℤ | ∃ f ∈ W, circleFourierCoeff f n ≠ 0}.Finite :=
  finite_fourier_support_of_invariant_finiteDimensional W θ
    (fourier_injective_of_irrational_rotation θ hθ) hW

/-- All-rotation invariance yields finite Fourier support without any extra
choice-of-angle assumption. -/
theorem finite_fourier_support_of_rotation_invariance
    (W : Submodule ℂ (Lp ℂ 2 circleMeasure)) [FiniteDimensional ℂ W]
    (hW : ∀ θ : ℝ, ∀ f ∈ W, boundaryRotation θ f ∈ W) :
    {n : ℤ | ∃ f ∈ W, circleFourierCoeff f n ≠ 0}.Finite := by
  apply finite_fourier_support_of_irrational_invariance W (Real.sqrt 2 * (2 * Real.pi))
  · simpa only [mul_div_cancel_right₀ _ Real.two_pi_pos.ne'] using irrational_sqrt_two
  · exact hW _

end KsIndex.Trace
