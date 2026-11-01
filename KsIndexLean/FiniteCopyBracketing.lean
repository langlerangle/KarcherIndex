module

public import KsIndexLean.VariationalBracketing

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

/-- The actual form-domain inclusion, retaining every copy in its original order. -/
def finiteH1Inclusion {ι : Type*} [Fintype ι]
    {D F : Submodule ℂ (ι → ComplexH1)} (h : D ≤ F) :
    finiteH1Domain D →ₗ[ℂ] finiteH1Domain F :=
  Submodule.inclusion (show finiteH1Domain D ≤ finiteH1Domain F from fun _ hu => h hu)

lemma finiteH1Inclusion_injective {ι : Type*} [Fintype ι]
    {D F : Submodule ℂ (ι → ComplexH1)} (h : D ≤ F) :
    Function.Injective (finiteH1Inclusion h) :=
  Submodule.inclusion_injective _

/-- Enlarging a finite-copy form domain lowers each available ordered eigenvalue.
This first instance treats infinite sectors; finite alternatives follow separately. -/
lemma finiteCopy_infinite_eigenvalue_le {ι : Type*} [Fintype ι]
    (D F : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] [CompleteSpace (finiteH1Domain F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [Infinite (finiteSpectralData D V).eigenbasisIndex]
    [Infinite (finiteSpectralData F V).eigenbasisIndex] (n : ℕ) :
    (finiteSpectralData F V).infiniteReciprocalShift (V.C + 1) n ≤
      (finiteSpectralData D V).infiniteReciprocalShift (V.C + 1) n := by
  exact eigenvalue_le_of_trial_inclusion (finiteH1Inclusion h)
    (finiteH1Inclusion_injective h)
    (fun u => (finiteH1Jacobi D V u u).re)
    (fun u => ‖finiteH1WeightedValue D u‖ ^ 2)
    (fun u => (finiteH1Jacobi F V u u).re)
    (fun u => ‖finiteH1WeightedValue F u‖ ^ 2)
    (fun _ => rfl) (fun _ => rfl) (n + 1) _ _
    (finiteCopyJacobi_infinite_minmax D V n)
    (finiteCopyJacobi_infinite_minmax F V n)

lemma finiteCopy_finite_eigenvalue_le {ι : Type*} [Fintype ι]
    (D F : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] [CompleteSpace (finiteH1Domain F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [FiniteDimensional ℂ (WeightedFiniteAmbient D)]
    [FiniteDimensional ℂ (WeightedFiniteAmbient F)] (n : ℕ)
    (hD : n < Module.finrank ℂ (WeightedFiniteAmbient D))
    (hF : n < Module.finrank ℂ (WeightedFiniteAmbient F)) :
    (finiteSpectralData F V).finiteReciprocalShift (V.C + 1) ⟨n, hF⟩ ≤
      (finiteSpectralData D V).finiteReciprocalShift (V.C + 1) ⟨n, hD⟩ := by
  exact eigenvalue_le_of_trial_inclusion (finiteH1Inclusion h)
    (finiteH1Inclusion_injective h)
    (fun u => (finiteH1Jacobi D V u u).re)
    (fun u => ‖finiteH1WeightedValue D u‖ ^ 2)
    (fun u => (finiteH1Jacobi F V u u).re)
    (fun u => ‖finiteH1WeightedValue F u‖ ^ 2)
    (fun _ => rfl) (fun _ => rfl) (n + 1) _ _
    (finiteCopyJacobi_finite_minmax D V ⟨n, hD⟩)
    (finiteCopyJacobi_finite_minmax F V ⟨n, hF⟩)

lemma finiteCopy_finite_to_infinite_eigenvalue_le {ι : Type*} [Fintype ι]
    (D F : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] [CompleteSpace (finiteH1Domain F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [FiniteDimensional ℂ (WeightedFiniteAmbient D)]
    [Infinite (finiteSpectralData F V).eigenbasisIndex] (n : ℕ)
    (hD : n < Module.finrank ℂ (WeightedFiniteAmbient D)) :
    (finiteSpectralData F V).infiniteReciprocalShift (V.C + 1) n ≤
      (finiteSpectralData D V).finiteReciprocalShift (V.C + 1) ⟨n, hD⟩ := by
  exact eigenvalue_le_of_trial_inclusion (finiteH1Inclusion h)
    (finiteH1Inclusion_injective h)
    (fun u => (finiteH1Jacobi D V u u).re)
    (fun u => ‖finiteH1WeightedValue D u‖ ^ 2)
    (fun u => (finiteH1Jacobi F V u u).re)
    (fun u => ‖finiteH1WeightedValue F u‖ ^ 2)
    (fun _ => rfl) (fun _ => rfl) (n + 1) _ _
    (finiteCopyJacobi_finite_minmax D V ⟨n, hD⟩)
    (finiteCopyJacobi_infinite_minmax F V n)

lemma finiteCopy_infinite_to_finite_eigenvalue_le {ι : Type*} [Fintype ι]
    (D F : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] [CompleteSpace (finiteH1Domain F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [Infinite (finiteSpectralData D V).eigenbasisIndex]
    [FiniteDimensional ℂ (WeightedFiniteAmbient F)] (n : ℕ)
    (hF : n < Module.finrank ℂ (WeightedFiniteAmbient F)) :
    (finiteSpectralData F V).finiteReciprocalShift (V.C + 1) ⟨n, hF⟩ ≤
      (finiteSpectralData D V).infiniteReciprocalShift (V.C + 1) n := by
  exact eigenvalue_le_of_trial_inclusion (finiteH1Inclusion h)
    (finiteH1Inclusion_injective h)
    (fun u => (finiteH1Jacobi D V u u).re)
    (fun u => ‖finiteH1WeightedValue D u‖ ^ 2)
    (fun u => (finiteH1Jacobi F V u u).re)
    (fun u => ‖finiteH1WeightedValue F u‖ ^ 2)
    (fun _ => rfl) (fun _ => rfl) (n + 1) _ _
    (finiteCopyJacobi_infinite_minmax D V n)
    (finiteCopyJacobi_finite_minmax F V ⟨n, hF⟩)

end KsIndex.Spectral
