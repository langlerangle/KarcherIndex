module

public import KsIndexLean.CompactFormKernel

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

/-- Pullback of a bounded conjugate-first form along its actual coordinate map. -/
def pullbackForm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (B : F →L⋆[ℂ] F →L[ℂ] ℂ) (A : E →L[ℂ] F) : E →L⋆[ℂ] E →L[ℂ] ℂ :=
  ((ContinuousLinearMap.compL ℂ E F ℂ).flip A).comp (B.comp A)

variable {ι : Type*} [Fintype ι]

def finiteDomainCopy (D : Submodule ℂ (ι → ComplexH1)) (i : ι) :
    finiteH1Domain D →L[ℂ] ComplexH1 :=
  (ContinuousLinearMap.proj i).comp (D.subtypeL.comp (finiteH1DomainCoordinates D))

lemma finiteDomainCopy_apply (D : Submodule ℂ (ι → ComplexH1)) (i : ι)
    (u : finiteH1Domain D) : finiteDomainCopy D i u = u.val i := rfl

/-- The actual ordered sum of disk Jacobi forms, now bounded and sesquilinear. -/
def finiteJacobiForm (D : Submodule ℂ (ι → ComplexH1)) (V : BoundedRealPotential) :
    finiteH1Domain D →L⋆[ℂ] finiteH1Domain D →L[ℂ] ℂ :=
  ∑ i, pullbackForm (E := finiteH1Domain D) (F := ComplexH1) (diskJacobiForm V) (finiteDomainCopy D i)

lemma finiteJacobiForm_apply (D : Submodule ℂ (ι → ComplexH1)) (V : BoundedRealPotential)
    (u v : finiteH1Domain D) : finiteJacobiForm D V u v = finiteH1Jacobi D V u v := by
  simp only [finiteJacobiForm, sum_apply]
  rfl

lemma finiteJacobiForm_hermitian (D : Submodule ℂ (ι → ComplexH1)) (V : BoundedRealPotential)
    (u v : finiteH1Domain D) : star (finiteJacobiForm D V v u) = finiteJacobiForm D V u v := by
  simp only [finiteJacobiForm_apply, finiteH1Jacobi, star_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact weakJacobi_conj V (u.val i) (v.val i)

/-- Shift by the actual finite weighted bulk mass inner product. -/
def shiftedFiniteForm (D : Submodule ℂ (ι → ComplexH1)) (V : BoundedRealPotential) :
    finiteH1Domain D →L⋆[ℂ] finiteH1Domain D →L[ℂ] ℂ :=
  finiteJacobiForm D V + (V.C + 1 : ℂ) •
    @mapPairing (finiteH1Domain D) (WeightedFiniteAmbient D)
      inferInstance (SubmoduleClass.toNormedSpace (finiteH1Domain D))
      inferInstance inferInstance
      (finiteH1WeightedValue D) (finiteH1WeightedValue D)

lemma shiftedFiniteForm_apply (D : Submodule ℂ (ι → ComplexH1)) (V : BoundedRealPotential)
    (u v : finiteH1Domain D) : shiftedFiniteForm D V u v = finiteH1Jacobi D V u v +
      (V.C + 1 : ℂ) * inner ℂ (finiteH1WeightedValue D u) (finiteH1WeightedValue D v) := by
  simp only [shiftedFiniteForm, add_apply, smul_apply, smul_eq_mul,
    finiteJacobiForm_apply]
  rfl

lemma shiftedFiniteForm_coercive (D : Submodule ℂ (ι → ComplexH1)) (V : BoundedRealPotential)
    (u : finiteH1Domain D) : ‖u‖ ^ 2 ≤ (shiftedFiniteForm D V u u).re := by
  have h := finiteH1Weighted_shift_coercive D V u
  rw [shiftedFiniteForm_apply, inner_self_eq_norm_sq_to_K]
  change ‖u‖ ^ 2 ≤ (finiteH1Jacobi D V u u + (V.C + 1 : ℂ) *
    (‖finiteH1WeightedValue D u‖ : ℂ) ^ 2).re
  simpa only [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_re, Complex.one_im, ← Complex.ofReal_pow,
    zero_add, add_zero, zero_mul, sub_zero] using h

lemma shiftedFiniteForm_hermitian (D : Submodule ℂ (ι → ComplexH1)) (V : BoundedRealPotential)
    (u v : finiteH1Domain D) : star (shiftedFiniteForm D V v u) = shiftedFiniteForm D V u v := by
  have hq : star (finiteH1Jacobi D V v u) = finiteH1Jacobi D V u v :=
    by simpa only [finiteJacobiForm_apply] using finiteJacobiForm_hermitian D V u v
  have hi : star (inner ℂ (finiteH1WeightedValue D v) (finiteH1WeightedValue D u)) =
      inner ℂ (finiteH1WeightedValue D u) (finiteH1WeightedValue D v) := inner_conj_symm _ _
  have hs (a b x y : ℂ) (c : ℝ) (ha : star a = b) (hx : star x = y) :
      star (a + (c : ℂ) * x) = b + (c : ℂ) * y := by
    simp only [star_add, star_mul, ha, hx, Complex.star_def, Complex.conj_ofReal]
    ring
  simpa only [shiftedFiniteForm_apply, Complex.ofReal_add, Complex.ofReal_one] using
    hs _ _ _ _ (V.C + 1) hq hi

end KsIndex.Spectral
