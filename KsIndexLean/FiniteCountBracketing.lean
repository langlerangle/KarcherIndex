module

public import KsIndexLean.SpectralCountBracketing
public import KsIndexLean.FiniteCopyNegativeIndex
public import KsIndexLean.FiniteCopyFiniteNegativeIndex
public import KsIndexLean.FiniteCopyNonpositiveCount
public import KsIndexLean.FiniteCopyFiniteNonpositiveCount

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

/-- An attained nonpositive subspace in the smaller domain fits beneath every
nonpositive dimension bound in the larger domain. This includes zero dimensions. -/
lemma nonpositive_count_le_of_inclusion
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (T : E →ₗ[ℂ] F) (hT : Function.Injective T) (Q : E → ℝ) (R : F → ℝ)
    (hQ : ∀ u, R (T u) = Q u) (d e : ℕ)
    (hd : ∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧ Module.finrank ℂ W = d ∧
      ∀ u : W, Q u ≤ 0)
    (he : ∀ W : Submodule ℂ F, FiniteDimensional ℂ W →
      (∀ u : W, R u ≤ 0) → Module.finrank ℂ W ≤ e) : d ≤ e := by
  have hd' : ∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧ Module.finrank ℂ W = d ∧
      ∀ u : W, Q u ≤ (0 : ℝ) * 0 := by simpa using hd
  obtain ⟨W, hfd, hdim, hbound⟩ :=
    trial_bound_transport T hT Q (fun _ => 0) R (fun _ => 0) hQ (fun _ => rfl) d 0 hd'
  have h := he W hfd (by simpa using hbound)
  exact hdim ▸ h

lemma finiteCopy_finite_nonpositive_count_le {ι : Type*} [Fintype ι]
    (D F : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] [CompleteSpace (finiteH1Domain F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [FiniteDimensional ℂ (WeightedFiniteAmbient D)] [FiniteDimensional ℂ (WeightedFiniteAmbient F)] :
    (finiteSpectralData D V).finiteWeakCount (V.C + 1) 0 ≤ (finiteSpectralData F V).finiteWeakCount (V.C + 1) 0 := by
  apply nonpositive_count_le_of_inclusion (finiteH1Inclusion h)
    (finiteH1Inclusion_injective h)
    (fun u => (finiteH1Jacobi D V u u).re)
    (fun u => (finiteH1Jacobi F V u u).re) (fun _ => rfl) _ _
    (finiteCopy_finite_nonpositive_dimension_attained D V)
  intro W hfd hW
  let := hfd
  exact finiteCopy_finite_nonpositive_dimension_le F V W hW

lemma finiteCopy_finite_to_infinite_nonpositive_count_le {ι : Type*} [Fintype ι]
    (D F : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] [CompleteSpace (finiteH1Domain F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [FiniteDimensional ℂ (WeightedFiniteAmbient D)] [Infinite (finiteSpectralData F V).eigenbasisIndex] :
    (finiteSpectralData D V).finiteWeakCount (V.C + 1) 0 ≤ finiteCopyNonpositiveCount F V := by
  apply nonpositive_count_le_of_inclusion (finiteH1Inclusion h)
    (finiteH1Inclusion_injective h)
    (fun u => (finiteH1Jacobi D V u u).re)
    (fun u => (finiteH1Jacobi F V u u).re) (fun _ => rfl) _ _
    (finiteCopy_finite_nonpositive_dimension_attained D V)
  intro W hfd hW
  let := hfd
  exact finiteCopy_nonpositive_dimension_le F V W hW

lemma finiteCopy_infinite_to_finite_nonpositive_count_le {ι : Type*} [Fintype ι]
    (D F : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] [CompleteSpace (finiteH1Domain F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [Infinite (finiteSpectralData D V).eigenbasisIndex] [FiniteDimensional ℂ (WeightedFiniteAmbient F)] :
    finiteCopyNonpositiveCount D V ≤ (finiteSpectralData F V).finiteWeakCount (V.C + 1) 0 := by
  apply nonpositive_count_le_of_inclusion (finiteH1Inclusion h)
    (finiteH1Inclusion_injective h)
    (fun u => (finiteH1Jacobi D V u u).re)
    (fun u => (finiteH1Jacobi F V u u).re) (fun _ => rfl) _ _
    (finiteCopy_nonpositive_count_attained D V)
  intro W hfd hW
  let := hfd
  exact finiteCopy_finite_nonpositive_dimension_le F V W hW


lemma finiteCopy_negativeIndex_le {ι : Type*} [Fintype ι]
    (D F : Submodule ℂ (ι → ComplexH1)) (V : BoundedRealPotential) (h : D ≤ F) :
    KsIndex.NegativeDensity.negativeIndex (fun u : finiteH1Domain D => (finiteH1Jacobi D V u u).re) ≤
    KsIndex.NegativeDensity.negativeIndex (fun u : finiteH1Domain F => (finiteH1Jacobi F V u u).re) := by
  have hz : (finiteH1Jacobi F V (0 : finiteH1Domain F) 0).re = 0 := by
    rw [← finiteJacobiForm_apply]
    exact congrArg (fun f : finiteH1Domain F →L[ℂ] ℂ => (f 0).re)
      ((finiteJacobiForm F V).toLinearMap.map_zero)
  exact KsIndex.NegativeDensity.negativeIndex_pullback_le
    (fun u : finiteH1Domain F => (finiteH1Jacobi F V u u).re) hz (finiteH1Inclusion h)

lemma finiteCopy_finite_negative_count_le {ι : Type*} [Fintype ι]
    (D F : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] [CompleteSpace (finiteH1Domain F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [FiniteDimensional ℂ (WeightedFiniteAmbient D)] [FiniteDimensional ℂ (WeightedFiniteAmbient F)] :
    (finiteSpectralData D V).finiteStrictCount (V.C + 1) 0 ≤ (finiteSpectralData F V).finiteStrictCount (V.C + 1) 0 := by
  have hh := finiteCopy_negativeIndex_le D F V h
  rw [finiteCopy_negativeIndex_eq_finite_count D V, finiteCopy_negativeIndex_eq_finite_count F V] at hh
  exact_mod_cast hh

lemma finiteCopy_finite_to_infinite_negative_count_le {ι : Type*} [Fintype ι]
    (D F : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] [CompleteSpace (finiteH1Domain F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [FiniteDimensional ℂ (WeightedFiniteAmbient D)] [Infinite (finiteSpectralData F V).eigenbasisIndex] :
    (finiteSpectralData D V).finiteStrictCount (V.C + 1) 0 ≤ finiteCopyNegativeCount F V := by
  have hh := finiteCopy_negativeIndex_le D F V h
  rw [finiteCopy_negativeIndex_eq_finite_count D V, finiteCopy_negativeIndex_eq_count F V] at hh
  exact_mod_cast hh

lemma finiteCopy_infinite_to_finite_negative_count_le {ι : Type*} [Fintype ι]
    (D F : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] [CompleteSpace (finiteH1Domain F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [Infinite (finiteSpectralData D V).eigenbasisIndex] [FiniteDimensional ℂ (WeightedFiniteAmbient F)] :
    finiteCopyNegativeCount D V ≤ (finiteSpectralData F V).finiteStrictCount (V.C + 1) 0 := by
  have hh := finiteCopy_negativeIndex_le D F V h
  rw [finiteCopy_negativeIndex_eq_count D V, finiteCopy_negativeIndex_eq_finite_count F V] at hh
  exact_mod_cast hh

end KsIndex.Spectral
