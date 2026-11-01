module

/-
Weak derivatives and sesquilinear forms under complex conjugation.

Both Cartesian derivatives commute with `conjH1`. Conjugating both arguments
conjugates the mass and Dirichlet forms and, for a bounded real potential, the
potential and weak Jacobi forms:

  `weakJacobi V (conjH1 u) (conjH1 v) = conj (weakJacobi V u v)`.

In particular, the real part of the diagonal form is unchanged. This supplies
the form identities used to transport negative index and nullity through a
conjugate-linear equivalence.
-/
public import KsIndexLean.ComplexH1ConjugationCovariance

@[expose] public section


noncomputable section
open scoped Real
open MeasureTheory
namespace KsIndex.WeakH1
open TauCeti

lemma W1p_gradient_neg (a : RealH1) : W1p.gradient (-a) = -(W1p.gradient a) := by
  rw [← W1p.gradientL_apply, ← W1p.gradientL_apply, map_neg]

lemma reLp_neg (f : L2C) : reLp (-f) = -reLp f := by rw [reLp, reLp, map_neg]
lemma imLp_neg (f : L2C) : imLp (-f) = -imLp f := by rw [imLp, imLp, map_neg]

/-- `star` on `L²(disk)` sends `joinLp a b` (i.e. `a + i b`) to `joinLp a (-b)`. -/
lemma joinLp_star (a b : L2R) : star (joinLp a b) = joinLp a (-b) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (joinLp a b), joinLp_ae a b, joinLp_ae a (-b),
    Lp.coeFn_neg b] with x h1 h2 h3 h4
  rw [h1, Pi.star_apply, h2, h3, h4, Pi.neg_apply]
  simp only [Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.ofReal_neg]
  ring

/-- **x-derivative covariance.** -/
lemma dxLp_conjH1 (u : ComplexH1) : dxLp (conjH1 u) = star (dxLp u) := by
  simp only [dxLp, conjH1_apply, rePart_conjMap, imPart_conjMap, W1p_gradient_neg, reLp_neg,
    joinLp_star]

/-- **y-derivative covariance.** -/
lemma dyLp_conjH1 (u : ComplexH1) : dyLp (conjH1 u) = star (dyLp u) := by
  simp only [dyLp, conjH1_apply, rePart_conjMap, imPart_conjMap, W1p_gradient_neg, imLp_neg,
    joinLp_star]

lemma dxCLM_conjH1 (u : ComplexH1) : dxCLM (conjH1 u) = star (dxCLM u) := dxLp_conjH1 u
lemma dyCLM_conjH1 (u : ComplexH1) : dyCLM (conjH1 u) = star (dyCLM u) := dyLp_conjH1 u

/-- **Anti-unitarity of the `L²(disk)` inner product under `star`.** -/
lemma inner_star_star_L2C (a b : L2C) :
    inner ℂ (star a) (star b) = (starRingEnd ℂ) (inner ℂ a b) := by
  rw [L2.inner_def, L2.inner_def, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star a, Lp.coeFn_star b] with x ha hb
  rw [ha, hb, Pi.star_apply, Pi.star_apply]
  simp only [RCLike.inner_apply, Complex.star_def, map_mul, Complex.conj_conj]

lemma valueCLM_conjH1_ae (u : ComplexH1) :
    (⇑(valueCLM (conjH1 u)) : ℂ → ℂ)
      =ᵐ[volume.restrict (disk : Set ℂ)] fun x => (starRingEnd ℂ) (valueCLM u x) := by
  rw [valueCLM_conjH1]
  filter_upwards [Lp.coeFn_star (valueCLM u)] with x hx
  rw [hx, Pi.star_apply, Complex.star_def]

/-- **Mass covariance.** -/
lemma mass_conjH1 (u v : ComplexH1) :
    mass (conjH1 u) (conjH1 v) = (starRingEnd ℂ) (mass u v) := by
  rw [mass, mass, valueCLM_conjH1, valueCLM_conjH1, inner_star_star_L2C]

/-- **Dirichlet form covariance.** -/
lemma dirichlet_conjH1 (u v : ComplexH1) :
    dirichlet (conjH1 u) (conjH1 v) = (starRingEnd ℂ) (dirichlet u v) := by
  simp only [dirichlet, dxCLM_conjH1, dyCLM_conjH1, inner_star_star_L2C, map_add]

/-- **Potential form covariance.** -/
lemma potential_conjH1 (V : BoundedRealPotential) (u v : ComplexH1) :
    potential V (conjH1 u) (conjH1 v) = (starRingEnd ℂ) (potential V u v) := by
  rw [potential_integral, potential_integral, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [valueCLM_conjH1_ae u, valueCLM_conjH1_ae v] with x hu hv
  rw [hu, hv]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]

/-- **Weak Jacobi form covariance:** conjugation on `ComplexH1` conjugates the sesquilinear form. -/
lemma weakJacobi_conjH1 (V : BoundedRealPotential) (u v : ComplexH1) :
    weakJacobi V (conjH1 u) (conjH1 v) = (starRingEnd ℂ) (weakJacobi V u v) := by
  simp only [weakJacobi, dirichlet_conjH1, potential_conjH1, map_sub]

end KsIndex.WeakH1
