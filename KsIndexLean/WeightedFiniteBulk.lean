module

public import KsIndexLean.SphericalBulkMap
public import KsIndexLean.BulkHilbertDomains

@[expose] public section


noncomputable section
namespace KsIndex.Spherical
open KsIndex.WeakH1 KsIndex.Spectral

abbrev WeightedFiniteL2 (ι : Type*) := PiLp 2 (fun _ : ι => WeightedDiskL2)

/-- Componentwise change to the actual spherical chart measure. -/
def finiteSphericalBulkCLM (ι : Type*) [Fintype ι] :
    (ι → L2C) →L[ℂ] WeightedFiniteL2 ι :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => WeightedDiskL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => sphericalBulkCLM.comp (ContinuousLinearMap.proj i)))

def weightedFiniteValueCLM (ι : Type*) [Fintype ι] :
    (ι → ComplexH1) →L[ℂ] WeightedFiniteL2 ι :=
  (finiteSphericalBulkCLM ι).comp (finiteDiskValueCLM ι)

lemma weightedFiniteValueCLM_compact (ι : Type*) [Fintype ι] :
    IsCompactOperator (weightedFiniteValueCLM ι) :=
  (finiteDiskValueCLM_compact ι).clm_comp (finiteSphericalBulkCLM ι)

lemma weightedFiniteValueCLM_apply (ι : Type*) [Fintype ι] (u : ι → ComplexH1) (i : ι) :
    weightedFiniteValueCLM ι u i = weightedDiskValueCLM (u i) := rfl

lemma weightedFiniteValueCLM_injective (ι : Type*) [Fintype ι] :
    Function.Injective (weightedFiniteValueCLM ι) := by
  intro u v h
  funext i
  exact weightedDiskValueCLM_injective (congrArg (fun f : WeightedFiniteL2 ι => f i) h)

lemma weightedFiniteValueCLM_norm_sq (ι : Type*) [Fintype ι] (u : ι → ComplexH1) :
    ‖weightedFiniteValueCLM ι u‖ ^ 2 = ∑ i, ‖weightedDiskValueCLM (u i)‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ _

/-- Shifted coercivity in the actual weighted summed mass, before domain restriction. -/
lemma weightedFinite_shift_coercive {ι : Type*} [Fintype ι]
    (V : BoundedRealPotential) (u : ι → ComplexH1) :
    (∑ i, ‖u i‖ ^ 2) ≤ (∑ i, weakJacobi V (u i) (u i)).re +
      (V.C + 1) * ‖weightedFiniteValueCLM ι u‖ ^ 2 := by
  apply sum_weakJacobi_shift_coercive V u
  rw [weightedFiniteValueCLM_norm_sq]
  apply Finset.sum_le_sum
  intro i _
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (norm_le_sphericalBulkCLM (valueCLM (u i)))

abbrev WeightedFiniteAmbient {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1)) :=
  bulkClosure (V := D) (H := WeightedFiniteL2 ι) ((weightedFiniteValueCLM ι).comp D.subtypeL)

abbrev weightedFiniteAmbientEmbedding {ι : Type*} [Fintype ι]
    (D : Submodule ℂ (ι → ComplexH1)) :=
  closureEmbedding (V := D) (H := WeightedFiniteL2 ι) ((weightedFiniteValueCLM ι).comp D.subtypeL)

lemma weightedFiniteAmbientEmbedding_spec {ι : Type*} [Fintype ι]
    (D : Submodule ℂ (ι → ComplexH1)) :
    Function.Injective (weightedFiniteAmbientEmbedding D) ∧
      DenseRange (weightedFiniteAmbientEmbedding D) ∧
      IsCompactOperator (weightedFiniteAmbientEmbedding D) :=
  ⟨closureEmbedding_injective (V := D)
      ((weightedFiniteValueCLM_injective ι).comp Subtype.val_injective),
    closureEmbedding_denseRange (V := D) _,
    closureEmbedding_compact (V := D) ((weightedFiniteValueCLM_compact ι).comp_clm D.subtypeL)⟩

lemma weightedFiniteAmbient_shift_coercive {ι : Type*} [Fintype ι]
    (D : Submodule ℂ (ι → ComplexH1)) (V : BoundedRealPotential) (u : D) :
    (∑ i, ‖u.val i‖ ^ 2) ≤ (∑ i, weakJacobi V (u.val i) (u.val i)).re +
      (V.C + 1) * ‖weightedFiniteAmbientEmbedding D u‖ ^ 2 :=
  weightedFinite_shift_coercive V u.val

end KsIndex.Spherical
