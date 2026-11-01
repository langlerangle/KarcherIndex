module

/-
Complex conjugation on `ComplexH1` as a conjugate-linear equivalence.

`ComplexH1 = WithLp 2 (RealH1 × RealH1)` carries the complex scalar action
`i • (re, im) = (-im, re)`. Conjugation negates the imaginary component and is
additive, involutive and semilinear over `starRingEnd ℂ`.

The value identities relate this operation to conjugation of the reconstructed
complex `L²` value, both as equality of `Lp` classes and almost-everywhere equality
of representatives. Rotation and trace compatibility are proved in
`ComplexH1ConjugationCovariance`; derivative and form identities are proved in
`ComplexH1ConjugationForm`.
-/
public import KsIndexLean.WeakH1Adapter

@[expose] public section


noncomputable section
open scoped Real
open MeasureTheory
namespace KsIndex.WeakH1
open TauCeti

/-- Underlying map of complex conjugation on `ComplexH1`: negate the imaginary part. -/
def conjMap (u : ComplexH1) : ComplexH1 := pair (rePart u) (-imPart u)

@[simp] lemma rePart_conjMap (u : ComplexH1) : rePart (conjMap u) = rePart u := rfl
@[simp] lemma imPart_conjMap (u : ComplexH1) : imPart (conjMap u) = -imPart u := rfl

/-- Extensionality of `ComplexH1` through its real/imaginary parts. -/
lemma complexH1_ext {u v : ComplexH1} (hr : rePart u = rePart v) (hi : imPart u = imPart v) :
    u = v := (WithLp.ext_iff 2).mpr (Prod.ext hr hi)

@[simp] lemma rePart_add (u v : ComplexH1) : rePart (u + v) = rePart u + rePart v := by
  simp only [rePart]; rfl
@[simp] lemma imPart_add (u v : ComplexH1) : imPart (u + v) = imPart u + imPart v := by
  simp only [imPart]; rfl

lemma conjMap_involutive : Function.Involutive conjMap := by
  intro u
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext <;> simp [conjMap, pair, rePart, imPart]

/-- **Complex conjugation on `ComplexH1`, bundled as a conjugate-linear equivalence.** -/
def conjH1 : ComplexH1 ≃ₛₗ[starRingEnd ℂ] ComplexH1 where
  toFun := conjMap
  invFun := conjMap
  left_inv := conjMap_involutive
  right_inv := conjMap_involutive
  map_add' u v := by
    refine complexH1_ext ?_ ?_
    · simp only [rePart_conjMap, rePart_add]
    · simp only [imPart_conjMap, imPart_add, neg_add]
  map_smul' c u :=
    complexH1_ext
      (by simp only [rePart_conjMap, complex_smul_re, imPart_conjMap, Complex.conj_re,
            Complex.conj_im]; module)
      (by simp only [imPart_conjMap, complex_smul_im, rePart_conjMap, Complex.conj_re,
            Complex.conj_im]; module)

@[simp] lemma conjH1_apply (u : ComplexH1) : conjH1 u = conjMap u := rfl

lemma rePart_conjH1 (u : ComplexH1) : rePart (conjH1 u) = rePart u := rfl
lemma imPart_conjH1 (u : ComplexH1) : imPart (conjH1 u) = -imPart u := rfl

/-- `W1p.value` respects negation (as an `Lp` equality). -/
lemma W1p_value_neg (a : RealH1) : W1p.value (-a) = -(W1p.value a) := by
  rw [← W1p.valueL_apply, ← W1p.valueL_apply, map_neg]

/-- **Master covariance (a.e. form).**  Conjugation acts on the reconstructed complex value
pointwise a.e. by complex conjugation. -/
lemma value_conjH1_ae (u : ComplexH1) :
    (fun x => value (conjH1 u) x)
      =ᵐ[volume.restrict (disk : Set ℂ)] fun x => (starRingEnd ℂ) (value u x) := by
  have hneg : (⇑(W1p.value (-imPart u)) : ℂ → ℝ)
      =ᵐ[volume.restrict (disk : Set ℂ)] (fun x => -(W1p.value (imPart u) x)) := by
    rw [W1p_value_neg]; exact Lp.coeFn_neg _
  filter_upwards [hneg] with x hx
  simp only [value, conjH1_apply, rePart_conjMap, imPart_conjMap, hx,
    Complex.ofReal_neg, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- **Master covariance (`Lp` form):** conjugation on `ComplexH1` is `star` on the reconstructed
complex `L²` value. -/
lemma valueLp_conjH1 (u : ComplexH1) : valueLp (conjH1 u) = star (valueLp u) := by
  apply Lp.ext
  refine (valueLp_ae (conjH1 u)).trans ((value_conjH1_ae u).trans ?_)
  filter_upwards [Lp.coeFn_star (valueLp u), valueLp_ae u] with x hx hxv
  rw [hx, Pi.star_apply, ← hxv]
  rfl

/-- **Master covariance (`valueCLM` form).** -/
lemma valueCLM_conjH1 (u : ComplexH1) : valueCLM (conjH1 u) = star (valueCLM u) := by
  change valueLp (conjH1 u) = star (valueLp u)
  exact valueLp_conjH1 u

end KsIndex.WeakH1
