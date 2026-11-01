module

public import KsIndexLean.CompactFormSolution

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Bounded conjugate-first pairing of two continuous complex-linear maps. -/
def mapPairing (A B : E →L[ℂ] F) : E →L⋆[ℂ] E →L[ℂ] ℂ :=
  ((ContinuousLinearMap.compL ℂ E F ℂ).flip B).comp ((innerSL ℂ).comp A)

lemma mapPairing_apply (A B : E →L[ℂ] F) (u v : E) :
    mapPairing A B u v = inner ℂ (A u) (B v) := rfl

/-- The actual adopted disk Jacobi form as a bounded sesquilinear form. -/
def diskJacobiForm (V : BoundedRealPotential) : ComplexH1 →L⋆[ℂ] ComplexH1 →L[ℂ] ℂ :=
  mapPairing dxCLM dxCLM + mapPairing dyCLM dyCLM -
    mapPairing valueCLM ((weightedCLM V).comp valueCLM)

lemma diskJacobiForm_apply (V : BoundedRealPotential) (u v : ComplexH1) :
    diskJacobiForm V u v = weakJacobi V u v := rfl

instance diskDomain_innerProductSpace (D : Submodule ℂ ComplexH1) : InnerProductSpace ℂ D :=
  Submodule.innerProductSpace (𝕜 := ℂ) (E := ComplexH1) D

/-- Restriction preserves the exact actual form and all inherited domain conditions. -/
def domainJacobiForm (D : Submodule ℂ ComplexH1) (V : BoundedRealPotential) :
    D →L⋆[ℂ] D →L[ℂ] ℂ :=
  mapPairing (E := D) (F := L2C) (dxCLM.comp D.subtypeL) (dxCLM.comp D.subtypeL) +
  mapPairing (E := D) (F := L2C) (dyCLM.comp D.subtypeL) (dyCLM.comp D.subtypeL) -
  mapPairing (E := D) (F := L2C) (valueCLM.comp D.subtypeL) ((weightedCLM V).comp (valueCLM.comp D.subtypeL))

lemma domainJacobiForm_apply (D : Submodule ℂ ComplexH1) (V : BoundedRealPotential) (u v : D) :
    domainJacobiForm D V u v = weakJacobi V u v := rfl

/-- Shift by the actual weighted ambient mass inner product. -/
def shiftedDiskForm (D : Submodule ℂ ComplexH1) (V : BoundedRealPotential) :
    D →L⋆[ℂ] D →L[ℂ] ℂ :=
  domainJacobiForm D V + (V.C + 1 : ℂ) •
    mapPairing (E := D) (F := WeightedDiskAmbient D) (weightedDiskAmbientEmbedding D) (weightedDiskAmbientEmbedding D)

lemma shiftedDiskForm_apply (D : Submodule ℂ ComplexH1) (V : BoundedRealPotential) (u v : D) :
    shiftedDiskForm D V u v = weakJacobi V u v + (V.C + 1 : ℂ) *
      inner ℂ (weightedDiskAmbientEmbedding D u) (weightedDiskAmbientEmbedding D v) := rfl

lemma shiftedDiskForm_coercive (D : Submodule ℂ ComplexH1) (V : BoundedRealPotential) (u : D) :
    ‖u‖ ^ 2 ≤ (shiftedDiskForm D V u u).re := by
  have h := weightedDiskAmbient_shift_coercive D V u
  rw [shiftedDiskForm_apply, inner_self_eq_norm_sq_to_K]
  change ‖u‖ ^ 2 ≤ (weakJacobi V u u + (V.C + 1 : ℂ) *
    (‖weightedDiskAmbientEmbedding D u‖ : ℂ) ^ 2).re
  simpa only [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_re, Complex.one_im, ← Complex.ofReal_pow,
    zero_add, add_zero, zero_mul, sub_zero] using h

private lemma hermitian_shift_scalar (a b x y : ℂ) (c : ℝ)
    (ha : star a = b) (hx : star x = y) :
    star (a + (c : ℂ) * x) = b + (c : ℂ) * y := by
  simp only [star_add, star_mul, ha, hx, Complex.star_def, Complex.conj_ofReal]
  ring

lemma shiftedDiskForm_hermitian (D : Submodule ℂ ComplexH1) (V : BoundedRealPotential) (u v : D) :
    star (shiftedDiskForm D V v u) = shiftedDiskForm D V u v := by
  have hq : star (weakJacobi V v u) = weakJacobi V u v := weakJacobi_conj V u v
  have hi : star (inner ℂ (weightedDiskAmbientEmbedding D v) (weightedDiskAmbientEmbedding D u)) =
      inner ℂ (weightedDiskAmbientEmbedding D u) (weightedDiskAmbientEmbedding D v) :=
    inner_conj_symm _ _
  simpa only [shiftedDiskForm_apply, Complex.ofReal_add, Complex.ofReal_one] using
    hermitian_shift_scalar _ _ _ _ (V.C + 1) hq hi

end KsIndex.Spectral
