module

public import KsIndexLean.DiskSolutionOperator

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace E] [CompleteSpace H] in
lemma eq_zero_of_inner_denseRange (J : E →L[ℂ] H) (hd : DenseRange J) (f : H)
    (hf : ∀ v, inner ℂ f (J v) = 0) : f = 0 := by
  have hall : ∀ y : H, inner ℂ f y = 0 := by
    intro y
    exact hd.induction_on y (p := fun y => inner ℂ f y = 0)
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const) hf
  exact inner_self_eq_zero.mp (hall f)

lemma formSolution_injective (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H) (hd : DenseRange J) :
    Function.Injective (formSolution B hB J) := by
  apply (formSolution B hB J).toLinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro f hf
  change formSolution B hB J f = 0 at hf
  apply eq_zero_of_inner_denseRange J hd f
  intro v
  have he := formSolution_weak B hB J f v
  rw [hf, map_zero, zero_apply] at he
  exact he.symm

lemma compactFormSolution_injective (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (hi : Function.Injective J) (hd : DenseRange J) :
    Function.Injective (compactFormSolution B hB J) :=
  hi.comp (formSolution_injective B hB J hd)

lemma compactFormSolution_strictPositive (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H) (hd : DenseRange J)
    {f : H} (hf : f ≠ 0) : 0 < (inner ℂ f (compactFormSolution B hB J f)).re := by
  have hr : formSolution B hB J f ≠ 0 := by
    intro hz
    apply hf
    apply formSolution_injective B hB J hd
    simpa using hz
  have he := formSolution_weak B hB J f (formSolution B hB J f)
  have hc := hB (formSolution B hB J f)
  rw [he] at hc
  exact (sq_pos_of_pos (norm_pos_iff.mpr hr)).trans_le hc

lemma selfAdjoint_injective_denseRange (T : H →L[ℂ] H)
    (hs : IsSelfAdjoint T) (hi : Function.Injective T) : DenseRange T := by
  have hk : T.ker = ⊥ := LinearMap.ker_eq_bot.mpr hi
  have ha : T.adjoint = T := ContinuousLinearMap.isSelfAdjoint_iff'.mp hs
  have hc := T.orthogonal_ker
  rw [hk, ha, Submodule.bot_orthogonal_eq_top] at hc
  change Dense (T.range : Set H)
  rw [dense_iff_closure_eq]
  exact congrArg (fun S : Submodule ℂ H => (S : Set H)) hc.symm

open KsIndex.WeakH1 KsIndex.Spherical

lemma diskSolutionOperator_injective (D : Submodule ℂ ComplexH1) [CompleteSpace D]
    (V : BoundedRealPotential) : Function.Injective (diskSolutionOperator D V) := by
  have h := @compactFormSolution_injective D (WeightedDiskAmbient D)
    inferInstance (diskDomain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance
    (shiftedDiskForm D V) (shiftedDiskForm_coercive D V) (weightedDiskAmbientEmbedding D)
    (weightedDiskAmbientEmbedding_spec D).1 (weightedDiskAmbientEmbedding_spec D).2.1
  exact h

lemma diskSolutionOperator_strictPositive (D : Submodule ℂ ComplexH1) [CompleteSpace D]
    (V : BoundedRealPotential) {f : WeightedDiskAmbient D} (hf : f ≠ 0) :
    0 < (inner ℂ f (diskSolutionOperator D V f)).re := by
  have h := @compactFormSolution_strictPositive D (WeightedDiskAmbient D)
    inferInstance (diskDomain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance
    (shiftedDiskForm D V) (shiftedDiskForm_coercive D V) (weightedDiskAmbientEmbedding D)
    (weightedDiskAmbientEmbedding_spec D).2.1 f hf
  exact h

lemma diskSolutionOperator_denseRange (D : Submodule ℂ ComplexH1) [CompleteSpace D]
    (V : BoundedRealPotential) : DenseRange (diskSolutionOperator D V) :=
  selfAdjoint_injective_denseRange _ (diskSolutionOperator_selfAdjoint D V)
    (diskSolutionOperator_injective D V)

end KsIndex.Spectral
