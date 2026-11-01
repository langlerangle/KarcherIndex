module

public import KsIndexLean.WeightedFiniteBulk

@[expose] public section


noncomputable section
open Set
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

abbrev FiniteH1 (ι : Type*) := PiLp 2 (fun _ : ι => ComplexH1)

/-- The same actual domain equations, with the finite Hilbert sum norm. -/
def finiteH1Domain {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1)) :
    Submodule ℂ (FiniteH1 ι) :=
  D.comap (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => ComplexH1)).toLinearMap

instance finiteH1Domain_innerProductSpace {ι : Type*} [Fintype ι]
    (D : Submodule ℂ (ι → ComplexH1)) : InnerProductSpace ℂ (finiteH1Domain D) :=
  Submodule.innerProductSpace (𝕜 := ℂ) (E := FiniteH1 ι) (finiteH1Domain D)

lemma finiteH1Domain_closed {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1))
    (hD : IsClosed (D : Set (ι → ComplexH1))) : IsClosed (finiteH1Domain D : Set (FiniteH1 ι)) :=
  hD.preimage (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => ComplexH1)).continuous

/-- Coordinate map into the original domain, preserving every boundary equation. -/
def finiteH1DomainCoordinates {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1)) :
    finiteH1Domain D →L[ℂ] D :=
  (((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => ComplexH1)).toContinuousLinearMap).comp
    (finiteH1Domain D).subtypeL).codRestrict D (fun u => u.property)

lemma finiteH1DomainCoordinates_bijective {ι : Type*} [Fintype ι]
    (D : Submodule ℂ (ι → ComplexH1)) : Function.Bijective (finiteH1DomainCoordinates D) := by
  constructor
  · intro u v h
    apply Subtype.ext
    apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => ComplexH1)).injective
    exact congrArg Subtype.val h
  · intro u
    refine ⟨⟨WithLp.toLp 2 u.val, ?_⟩, ?_⟩
    · exact u.property
    · rfl

def finiteH1WeightedValue {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1)) :
    finiteH1Domain D →L[ℂ] WeightedFiniteAmbient D :=
  (weightedFiniteAmbientEmbedding D).comp (finiteH1DomainCoordinates D)

lemma finiteH1WeightedValue_spec {ι : Type*} [Fintype ι]
    (D : Submodule ℂ (ι → ComplexH1)) :
    Function.Injective (finiteH1WeightedValue D) ∧ DenseRange (finiteH1WeightedValue D) ∧
      IsCompactOperator (finiteH1WeightedValue D) := by
  obtain ⟨hi, hd, hc⟩ := weightedFiniteAmbientEmbedding_spec D
  refine ⟨hi.comp (finiteH1DomainCoordinates_bijective D).1, ?_,
    hc.comp_clm (finiteH1DomainCoordinates D)⟩
  exact hd.comp (finiteH1DomainCoordinates_bijective D).2.denseRange (weightedFiniteAmbientEmbedding D).continuous

def finiteH1Jacobi {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1))
    (V : BoundedRealPotential) (u v : finiteH1Domain D) : ℂ :=
  ∑ i, weakJacobi V (u.val i) (v.val i)

lemma finiteH1Weighted_shift_coercive {ι : Type*} [Fintype ι]
    (D : Submodule ℂ (ι → ComplexH1)) (V : BoundedRealPotential) (u : finiteH1Domain D) :
    ‖u‖ ^ 2 ≤ (finiteH1Jacobi D V u u).re + (V.C + 1) * ‖finiteH1WeightedValue D u‖ ^ 2 := by
  have h := weightedFiniteAmbient_shift_coercive D V (finiteH1DomainCoordinates D u)
  change ‖u.val‖ ^ 2 ≤ _
  rw [PiLp.norm_sq_eq_of_L2]
  exact h

lemma finiteH1Domain_completeSpace {ι : Type*} [Fintype ι]
    (D : Submodule ℂ (ι → ComplexH1)) (hD : IsClosed (D : Set (ι → ComplexH1))) :
    CompleteSpace (finiteH1Domain D) :=
  (finiteH1Domain_closed D hD).isComplete.completeSpace_coe

end KsIndex.Spectral
