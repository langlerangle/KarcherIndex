module

/-
Conjugate-linear transfer of negative index and nullity.

These lemmas complement the complex-linear congruence results in `DtnBridge`.
They apply to equivalences semilinear over `starRingEnd ℂ`, including the complex
conjugation that relates opposite rotation classes in the sector applications.

A conjugate-linear equivalence is real-linear. For finite-dimensional complex
spaces, the real dimension formula therefore gives equality of complex dimensions.
The index and nullity arguments apply this fact to finite-dimensional subspaces;
the ambient spaces need not be finite-dimensional.

Negative-index transfer assumes the explicit identity `Q' (e x) = Q x` for the
real-valued functions. Nullity transfer assumes
`B' (e x) (e y) = conj (B x y)`, so vanishing against all arguments is preserved.
The abstract transfer lemmas do not impose additional quadratic or sesquilinear
hypotheses on these functions. Applying the comparison in both directions yields
the corresponding equalities.
-/
public import KsIndexLean.DtnBridge

@[expose] public section


noncomputable section
open KsIndex.NegativeDensity

namespace KsIndex.DtnBridge

section ConjTransfer
variable {X Y : Type*} [AddCommGroup X] [Module ℂ X] [Module ℝ X] [IsScalarTower ℝ ℂ X]
  [AddCommGroup Y] [Module ℂ Y] [Module ℝ Y] [IsScalarTower ℝ ℂ Y]

/-- A conjugate-linear equivalence is in particular ℝ-linear (conjugation fixes `ℝ`). -/
def conjToReal (f : X ≃ₛₗ[starRingEnd ℂ] Y) : X ≃ₗ[ℝ] Y :=
  { f.toAddEquiv with
    map_smul' := fun (r : ℝ) a => by
      change f (r • a) = r • f a
      rw [← algebraMap_smul ℂ r a, map_smulₛₗ, ← algebraMap_smul ℂ r (f a)]
      congr 1
      simp }

/-- A conjugate-linear equivalence preserves finite-dimensionality over `ℂ`. -/
lemma conjLinearEquiv_finiteDimensional (f : X ≃ₛₗ[starRingEnd ℂ] Y)
    [FiniteDimensional ℂ X] : FiniteDimensional ℂ Y := by
  have : FiniteDimensional ℝ X := Module.Finite.trans ℂ X
  have : FiniteDimensional ℝ Y := (conjToReal f).finiteDimensional
  exact Module.Finite.of_restrictScalars_finite ℝ ℂ Y

/-- A conjugate-linear equivalence preserves `finrank ℂ` (via the real dimension). -/
lemma conjLinearEquiv_finrank_eq (f : X ≃ₛₗ[starRingEnd ℂ] Y) [FiniteDimensional ℂ X] :
    Module.finrank ℂ X = Module.finrank ℂ Y := by
  have : FiniteDimensional ℝ X := Module.Finite.trans ℂ X
  have : FiniteDimensional ℂ Y := conjLinearEquiv_finiteDimensional f
  have h2X : Module.finrank ℝ ℂ * Module.finrank ℂ X = Module.finrank ℝ X :=
    Module.finrank_mul_finrank ℝ ℂ X
  have h2Y : Module.finrank ℝ ℂ * Module.finrank ℂ Y = Module.finrank ℝ Y :=
    Module.finrank_mul_finrank ℝ ℂ Y
  have hR : Module.finrank ℝ X = Module.finrank ℝ Y := (conjToReal f).finrank_eq
  have hne : Module.finrank ℝ ℂ ≠ 0 := by rw [Complex.finrank_real_complex]; norm_num
  have hmul : Module.finrank ℝ ℂ * Module.finrank ℂ X
      = Module.finrank ℝ ℂ * Module.finrank ℂ Y := by rw [h2X, hR, ← h2Y]
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) hmul

/-- Conjugate-linear analogue of `negativeIndex_le_of_equiv`: the real-valued functions
satisfy `Q' (e x) = Q x`, so their negative indices compare across the equivalence. -/
lemma negativeIndex_le_of_equiv_conj (e : X ≃ₛₗ[starRingEnd ℂ] Y)
    (Q : X → ℝ) (Q' : Y → ℝ) (h : ∀ x, Q' (e x) = Q x) :
    negativeIndex Q ≤ negativeIndex Q' := by
  unfold negativeIndex
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfin => ?_
  let := hfin
  let eV := Submodule.equivMapOfInjective (e : X →ₛₗ[starRingEnd ℂ] Y) e.injective V
  have hfd : FiniteDimensional ℂ (V.map (e : X →ₛₗ[starRingEnd ℂ] Y)) :=
    conjLinearEquiv_finiteDimensional eV
  refine le_iSup_of_le (V.map (e : X →ₛₗ[starRingEnd ℂ] Y)) (le_iSup_of_le ?_
    (le_iSup_of_le hfd ?_))
  · rintro y ⟨x, hx, rfl⟩ hy
    show Q' ((e : X →ₛₗ[starRingEnd ℂ] Y) x) < 0
    rw [show ((e : X →ₛₗ[starRingEnd ℂ] Y) x) = e x from rfl, h]
    exact hV x hx (fun hz => hy (by rw [hz, map_zero]))
  · rw [← conjLinearEquiv_finrank_eq eV]

/-- Conjugate-linear congruence for the negative index. -/
lemma negativeIndex_congr_conj (e : X ≃ₛₗ[starRingEnd ℂ] Y)
    (Q : X → ℝ) (Q' : Y → ℝ) (h : ∀ x, Q' (e x) = Q x) :
    negativeIndex Q' = negativeIndex Q := by
  refine le_antisymm (negativeIndex_le_of_equiv_conj e.symm Q' Q fun y => ?_)
    (negativeIndex_le_of_equiv_conj e Q Q' h)
  rw [← h (e.symm y), e.apply_symm_apply]

/-- Conjugate-linear analogue of `sesqNullity_le_of_equiv`: a conj-linear
intertwiner `B' (e x) (e y) = conj (B x y)` carries the radical (zero-ness is
conj-invariant), and a conj-linear bijection preserves `finrank`. -/
lemma sesqNullity_le_of_equiv_conj (e : X ≃ₛₗ[starRingEnd ℂ] Y) (B : X → X → ℂ)
    (B' : Y → Y → ℂ) (h : ∀ x y, B' (e x) (e y) = starRingEnd ℂ (B x y)) :
    sesqNullity B ≤ sesqNullity B' := by
  unfold sesqNullity
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfin => ?_
  let := hfin
  let eV := Submodule.equivMapOfInjective (e : X →ₛₗ[starRingEnd ℂ] Y) e.injective V
  have hfd : FiniteDimensional ℂ (V.map (e : X →ₛₗ[starRingEnd ℂ] Y)) :=
    conjLinearEquiv_finiteDimensional eV
  refine le_iSup_of_le (V.map (e : X →ₛₗ[starRingEnd ℂ] Y)) (le_iSup_of_le ?_
    (le_iSup_of_le hfd ?_))
  · rintro y ⟨x, hx, rfl⟩ w
    have hxw := h x (e.symm w)
    rw [e.apply_symm_apply] at hxw
    change B' ((e : X →ₛₗ[starRingEnd ℂ] Y) x) w = 0
    rw [show ((e : X →ₛₗ[starRingEnd ℂ] Y) x) = e x from rfl, hxw, hV x hx (e.symm w),
      map_zero]
  · rw [← conjLinearEquiv_finrank_eq eV]

/-- Conjugate-linear congruence for the sesquilinear radical (nullity). -/
lemma sesqNullity_congr_conj (e : X ≃ₛₗ[starRingEnd ℂ] Y) (B : X → X → ℂ)
    (B' : Y → Y → ℂ) (h : ∀ x y, B' (e x) (e y) = starRingEnd ℂ (B x y)) :
    sesqNullity B' = sesqNullity B := by
  refine le_antisymm (sesqNullity_le_of_equiv_conj e.symm B' B fun x y => ?_)
    (sesqNullity_le_of_equiv_conj e B B' h)
  have hxy := h (e.symm x) (e.symm y)
  rw [e.apply_symm_apply, e.apply_symm_apply] at hxy
  rw [hxy, starRingEnd_self_apply]

end ConjTransfer

end KsIndex.DtnBridge
