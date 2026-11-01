module

/-
# Variational index under a dense form-preserving map

`formIndex_eq_negativeIndex` identifies the function-space index on a submodule
with the variational index of its subtype. It requires no regularity assumptions
on the quadratic function.

`formIndex_eq_of_dense_form_map` transports that index to a complex normed space
with a continuous Hermitian sesquilinear form. The linear map must have dense
range and preserve the quadratic form. It need not be injective: vectors in its
kernel have zero quadratic value and cannot lie in a negative-definite subspace.
Density supplies approximation of finite negative frames in the target.

The theorem keeps density and form agreement as hypotheses. Applications must
prove them for their particular function spaces; this module supplies the index
comparison once those analytic facts are available.
-/
public import KsIndexLean.NegativeDensity
public import KsIndexLean.FormIndex

@[expose] public section


noncomputable section

namespace KsIndex.FormIndex

open NegativeDensity

/-- Restricting the ambient vector space to the domain preserves the index. -/
theorem formIndex_eq_negativeIndex {ι : Type*} (Q : (ι → ℂ) → ℝ)
    (D : Submodule ℂ (ι → ℂ)) :
    formIndex Q D = negativeIndex (fun x : D => Q x.val) := by
  classical
  apply le_antisymm
  · unfold formIndex negativeIndex
    refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfin => ?_
    let := hfin
    let W := V.comap D.subtype
    let e : W ≃ₗ[ℂ] V := Submodule.comapSubtypeEquivOfLe hV.1
    have : FiniteDimensional ℂ W := FiniteDimensional.of_injective e.toLinearMap e.injective
    have hW : ∀ x ∈ W, x ≠ 0 → Q x.val < 0 := by
      intro x hx hn
      exact hV.2 x.val hx (fun h => hn (Subtype.ext h))
    rw [← e.finrank_eq]
    exact le_iSup_of_le W (le_iSup_of_le hW
      (le_iSup_of_le (inferInstance : FiniteDimensional ℂ W) le_rfl))
  · unfold formIndex negativeIndex
    refine iSup_le fun W => iSup_le fun hW => iSup_le fun hfin => ?_
    let := hfin
    let V := W.map D.subtype
    have hV : NegOn Q D V := by
      constructor
      · rintro x ⟨y, hy, rfl⟩
        exact y.property
      · rintro x ⟨y, hy, rfl⟩ hn
        exact hW y hy (fun h => hn (by simp [h]))
    have hdim : Module.finrank ℂ V = Module.finrank ℂ W :=
      Submodule.finrank_map_subtype_eq D W
    rw [← hdim]
    exact le_iSup_of_le V (le_iSup_of_le hV
      (le_iSup_of_le (inferInstance : FiniteDimensional ℂ V) le_rfl))

/-- A dense linear map preserving the quadratic form preserves its variational
index. `hB` includes continuity and Hermitian sesquilinearity. Neither injectivity
of `j` nor completeness of `E` is assumed. -/
theorem formIndex_eq_of_dense_form_map
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q : (ι → ℂ) → ℝ) (D : Submodule ℂ (ι → ℂ))
    {B : E → E → ℂ} (hB : NegativeDensity.Sesq B)
    (j : D →ₗ[ℂ] E) (hj : DenseRange j)
    (hform : ∀ x : D, Q x.val = (B (j x) (j x)).re) :
    formIndex Q D = negativeIndex (fun x => (B x x).re) := by
  rw [formIndex_eq_negativeIndex]
  simp_rw [hform]
  exact negativeIndex_pullback_of_denseRange hB j hj

end KsIndex.FormIndex
