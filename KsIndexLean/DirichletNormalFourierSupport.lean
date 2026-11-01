module

public import KsIndexLean.WeakNormalFourierFunctional

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical KsIndex.Spectral
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

local instance : CompleteSpace (zeroTraceDomain Set.univ) :=
  (isClosed_zeroTraceDomain Set.univ).completeSpace_coe

/-- Finite normal Fourier support, uniformly over the actual Dirichlet weak
eigenspace. The proof uses finite-dimensional dual eigenvectors, not an assumed
L2 normal trace. -/
theorem dirichlet_normal_functionals_finite (k : ℕ) (lam : ℝ) :
    {n : ℤ | ∃ u : zeroTraceDomain Set.univ,
      u ∈ diskWeakEigenspace (zeroTraceDomain Set.univ) (surfacePotential k) lam ∧
      weakNormalFourierFunctional k lam n u ≠ 0}.Finite := by
  let D := zeroTraceDomain Set.univ
  let E := diskWeakEigenspace D (surfacePotential k) lam
  let := diskWeakEigenspace_finiteDimensional D (surfacePotential k) lam
  let θ := Real.sqrt 2 * (2 * Real.pi)
  let T : E →ₗ[ℂ] E :=
    { toFun := fun u => ⟨⟨diskRotation θ (u : D),
        diskRotation_mem_fullZeroTrace θ u u.val.property⟩,
        diskWeakEigenspace_rotation D diskRotation_mem_fullZeroTrace k lam θ u u.property⟩
      map_add' := by intro u v; apply Subtype.ext; apply Subtype.ext; exact map_add (diskRotation θ) _ _
      map_smul' := by intro c u; apply Subtype.ext; apply Subtype.ext; exact map_smul (diskRotation θ) _ _ }
  let l : ℤ → E →ₗ[ℂ] ℂ := fun n =>
    (weakNormalFourierFunctional k lam n).comp (D.subtype.comp E.subtype)
  have hl (n : ℤ) (u : E) : l n (T u) =
      fourier n (θ : AddCircle (2 * Real.pi)) * l n u := by
    apply weakNormalFourierFunctional_rotation k lam θ u
    intro v hv
    exact (mem_diskWeakEigenspace_all D (surfacePotential k) lam u).mp u.property ⟨v, hv⟩
  have hi : Function.Injective (fun n : ℤ => fourier n (θ : AddCircle (2 * Real.pi))) := by
    apply fourier_injective_of_irrational_rotation
    simpa only [θ, mul_div_cancel_right₀ _ Real.two_pi_pos.ne'] using irrational_sqrt_two
  apply (finite_nonzero_eigenfunctionals T l _ hi hl).subset
  rintro n ⟨u, hu, hn⟩ hz
  exact hn (congrArg (fun L : E →ₗ[ℂ] ℂ => L ⟨u, hu⟩) hz)

/-- Every Dirichlet weak eigenfunction has finitely many nonzero canonical
normal coefficients, with no added boundary smoothness assumption. -/
theorem sphericalEigen_dirichlet_normal_finite_support (k : ℕ) (lam : ℝ)
    (u : ComplexH1) (ht : u ∈ zeroTraceDomain Set.univ)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v)) :
    {n : ℤ | eigenDiskNormalMode k lam u n ≠ 0}.Finite := by
  have he : (⟨u, ht⟩ : zeroTraceDomain Set.univ) ∈
      diskWeakEigenspace (zeroTraceDomain Set.univ) (surfacePotential k) lam :=
    (mem_diskWeakEigenspace_all _ _ _ _).mpr (fun v => hu v v.property)
  apply (dirichlet_normal_functionals_finite k lam).subset
  intro n hn
  refine ⟨⟨u, ht⟩, he, ?_⟩
  rw [weakNormalFourierFunctional_eq k lam u n hu]
  exact mul_ne_zero (by exact_mod_cast Real.two_pi_pos.ne') hn

end KsIndex.Trace
