module

public import KsIndexLean.FormIndexSum
public import KsIndexLean.NegativeDensity
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

@[expose] public section


/-! Zero energy implies orthogonality on a nonnegative Hermitian subspace.
The core is algebraic and reuses real symmetric Cauchy–Schwarz on the real part.
Orthogonality is concluded on the specified subspace W. Passing from a dense
test subspace to a larger form domain requires a separate extension argument;
no common-eigenfunction conclusion is asserted here. -/
noncomputable section
namespace KsIndex

/-- A W-scoped algebraic orthogonality lemma, with no topological assumptions.
The form is conjugate-linear in its first slot and linear in its second slot. -/
theorem hermitian_orthogonal_of_nonneg_diag
    {E : Type*} [AddCommGroup E] [Module ℂ E] (B : E → E → ℂ)
    (W : Submodule ℂ E)
    (haddL : ∀ x ∈ W, ∀ y ∈ W, ∀ z ∈ W, B (x + y) z = B x z + B y z)
    (haddR : ∀ x ∈ W, ∀ y ∈ W, ∀ z ∈ W, B x (y + z) = B x y + B x z)
    (hsmulR : ∀ c : ℂ, ∀ x ∈ W, ∀ y ∈ W, B x (c • y) = c * B x y)
    (hconj : ∀ x ∈ W, ∀ y ∈ W, B y x = (starRingEnd ℂ) (B x y))
    (hnonneg : ∀ x ∈ W, 0 ≤ (B x x).re)
    {u : E} (hu : u ∈ W) (hzero : (B u u).re = 0) :
    ∀ v ∈ W, B u v = 0 := by
  let : Module ℝ W := Module.compHom W Complex.ofRealHom
  have hsmulL : ∀ c : ℂ, ∀ x ∈ W, ∀ y ∈ W,
      B (c • x) y = (starRingEnd ℂ) c * B x y := by
    intro c x hx y hy
    rw [hconj y hy (c • x) (W.smul_mem c hx), hsmulR c y hy x hx,
      map_mul, ← hconj y hy x hx]
  let R : LinearMap.BilinForm ℝ W := LinearMap.mk₂ ℝ
    (fun x y : W => (B x.val y.val).re)
    (fun x y z => by simp only [Submodule.coe_add, haddL x x.property y y.property
      z z.property, Complex.add_re])
    (fun c x y => by
      change (B ((c : ℂ) • x.val) y.val).re = c * (B x.val y.val).re
      rw [hsmulL (c : ℂ) x x.property y y.property]
      simp)
    (fun x y z => by simp only [Submodule.coe_add, haddR x x.property y y.property
      z z.property, Complex.add_re])
    (fun c x y => by
      change (B x.val ((c : ℂ) • y.val)).re = c * (B x.val y.val).re
      rw [hsmulR (c : ℂ) x x.property y y.property]
      simp)
  have hR : LinearMap.IsSymm R := by
    constructor
    intro x y
    change (B x.val y.val).re = (B y.val x.val).re
    rw [hconj x x.property y y.property]
    rfl
  have hre : ∀ v ∈ W, (B u v).re = 0 := by
    intro v hv
    have h := R.apply_sq_le_of_symm (fun x => hnonneg x x.property) hR
      (⟨u, hu⟩ : W) (⟨v, hv⟩ : W)
    change (B u v).re ^ 2 ≤ (B u u).re * (B v v).re at h
    rw [hzero, zero_mul] at h
    nlinarith [sq_nonneg (B u v).re]
  intro v hv
  have hi := hre (Complex.I • v) (W.smul_mem Complex.I hv)
  rw [hsmulR Complex.I u hu v hv] at hi
  apply Complex.ext
  · exact hre v hv
  · simpa using hi

namespace FormIndex

/-- Restrict nonnegativity to W; the ambient form on D may be indefinite. -/
theorem Sesq.orthogonal_of_nonneg_of_eq_zero
    {ι : Type*} {Q : (ι → ℂ) → ℝ} {B : (ι → ℂ) → (ι → ℂ) → ℂ}
    {D W : Submodule ℂ (ι → ℂ)} (h : Sesq Q B D) (hWD : W ≤ D)
    (hnonneg : ∀ x ∈ W, 0 ≤ Q x) {u : ι → ℂ} (hu : u ∈ W) (hzero : Q u = 0) :
    ∀ v ∈ W, B u v = 0 :=
  hermitian_orthogonal_of_nonneg_diag B W
    (fun _ hx _ hy _ hz => h.addL (hWD hx) (hWD hy) (hWD hz))
    (fun _ hx _ hy _ hz => h.addR (hWD hx) (hWD hy) (hWD hz))
    (fun c _ hx _ hy => h.smulR c (hWD hx) (hWD hy))
    (fun x _ y _ => h.conj x y)
    (fun x hx => by simpa only [h.self, Complex.ofReal_re] using hnonneg x hx)
    hu (by simpa only [h.self, Complex.ofReal_re] using hzero)

end FormIndex
namespace NegativeDensity

/-- The continuous-form adapter uses only the algebraic fields of the existing structure. -/
theorem Sesq.orthogonal_of_nonneg_of_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : E → E → ℂ}
    (h : Sesq B) (W : Submodule ℂ E) (hnonneg : ∀ x ∈ W, 0 ≤ (B x x).re)
    {u : E} (hu : u ∈ W) (hzero : (B u u).re = 0) : ∀ v ∈ W, B u v = 0 :=
  hermitian_orthogonal_of_nonneg_diag B W
    (fun x _ y _ z _ => h.addL x y z) (fun x _ y _ z _ => h.addR x y z)
    (fun c x _ y _ => h.smulR c x y) (fun x _ y _ => h.conj x y) hnonneg hu hzero

end NegativeDensity
end KsIndex
