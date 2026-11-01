module

/-
# Explicit translation Jacobi fields

For `k ≥ 2`, the three Gauss-map components solve the flat Jacobi equation
`laplacian u + potV k · u = 0` on all of `ℂ`. This file develops the Wirtinger
calculus used to prove those identities and derives the geometric Jacobi
equations on the open unit disk by conformal rescaling.

The flat-equation proofs were produced with Harmonic's Aristotle. Global
seam compatibility, boundedness and linear independence are separate from
these local differential identities.
-/
public import Mathlib
public import KsIndexLean.Surface

@[expose] public section


open Complex KsIndex.Surface

noncomputable section

namespace KsIndex.JacobiFields

/-- Third Gauss-map component (vertical translation): `(|w|^{2k−2} − 1)/(|w|^{2k−2} + 1)`. -/
def nu3 (k : ℕ) (w : ℂ) : ℂ :=
  (((‖w‖ ^ (2 * k - 2) - 1) / (‖w‖ ^ (2 * k - 2) + 1) : ℝ) : ℂ)

/-- First Gauss-map component (horizontal translation): `2 Re(w^{k−1})/(|w|^{2k−2} + 1)`. -/
def nu1 (k : ℕ) (w : ℂ) : ℂ :=
  ((2 * (w ^ (k - 1)).re / (‖w‖ ^ (2 * k - 2) + 1) : ℝ) : ℂ)

/-- Second Gauss-map component (horizontal translation): `2 Im(w^{k−1})/(|w|^{2k−2} + 1)`. -/
def nu2 (k : ℕ) (w : ℂ) : ℂ :=
  ((2 * (w ^ (k - 1)).im / (‖w‖ ^ (2 * k - 2) + 1) : ℝ) : ℂ)

/-!
### Wirtinger calculus toolkit

Every function occurring below is a rational expression in `z ^ n` and `conj z ^ n`, so its real
Fréchet derivative at `w` has the form `v ↦ a * v + b * conj v`.  We record this data as
`HasWD f a b w` (`a = ∂_z f`, `b = ∂_z̄ f`) and develop the usual calculus rules for it; the flat
Laplacian is then `Δ f = 4 ∂_z ∂_z̄ f` (`laplacian_eq` below).
-/

def wlin (a b : ℂ) : ℂ →L[ℝ] ℂ :=
  a • (ContinuousLinearMap.id ℝ ℂ) + b • (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap
@[simp] lemma wlin_apply (a b z : ℂ) : wlin a b z = a * z + b * (starRingEnd ℂ) z := by
  simp [wlin, Complex.conjCLE]
def HasWD (f : ℂ → ℂ) (a b : ℂ) (w : ℂ) : Prop := HasFDerivAt f (wlin a b) w
lemma HasWD.congr {f : ℂ → ℂ} {a b a' b' w : ℂ} (h : HasWD f a b w) (ha : a = a') (hb : b = b') :
    HasWD f a' b' w := by subst ha; subst hb; exact h
lemma HasWD.congr_fun {f g : ℂ → ℂ} {a b w : ℂ} (h : HasWD f a b w) (hfg : f = g) :
    HasWD g a b w := hfg ▸ h
lemma hasWD_const (c w : ℂ) : HasWD (fun _ => c) 0 0 w := by
  have h : wlin 0 0 = 0 := by ext z; simp
  rw [HasWD, h]; exact hasFDerivAt_const c w
lemma hasWD_pow (n : ℕ) (w : ℂ) : HasWD (fun z => z ^ n) ((n : ℂ) * w ^ (n-1)) 0 w := by
  refine (((hasDerivAt_pow n w).hasFDerivAt).restrictScalars ℝ).congr_fderiv ?_
  ext z; simp; all_goals ring
lemma hasWD_conj_pow (n : ℕ) (w : ℂ) :
    HasWD (fun z => ((starRingEnd ℂ) z) ^ n) 0 ((n : ℂ) * ((starRingEnd ℂ) w) ^ (n-1)) w := by
  have h1 := ((hasDerivAt_pow n ((starRingEnd ℂ) w)).hasFDerivAt).restrictScalars ℝ
  have h2 : HasFDerivAt (fun z : ℂ => (starRingEnd ℂ) z)
      (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap w := Complex.conjCLE.hasFDerivAt
  refine ((h1.comp w h2)).congr_fderiv ?_
  ext z; simp [Complex.conjCLE]; all_goals ring
lemma HasWD.add {f g : ℂ → ℂ} {a b c d w : ℂ} (hf : HasWD f a b w) (hg : HasWD g c d w) :
    HasWD (fun z => f z + g z) (a + c) (b + d) w := by
  refine (HasFDerivAt.add hf hg).congr_fderiv ?_
  ext z; simp; all_goals ring
lemma HasWD.sub {f g : ℂ → ℂ} {a b c d w : ℂ} (hf : HasWD f a b w) (hg : HasWD g c d w) :
    HasWD (fun z => f z - g z) (a - c) (b - d) w := by
  refine (HasFDerivAt.sub hf hg).congr_fderiv ?_
  ext z; simp; all_goals ring
lemma HasWD.mul {f g : ℂ → ℂ} {a b c d w : ℂ} (hf : HasWD f a b w) (hg : HasWD g c d w) :
    HasWD (fun z => f z * g z) (f w * c + g w * a) (f w * d + g w * b) w := by
  refine (HasFDerivAt.mul hf hg).congr_fderiv ?_
  ext z; simp; all_goals ring
lemma HasWD.mul_const {f : ℂ → ℂ} {a b w : ℂ} (hf : HasWD f a b w) (c : ℂ) :
    HasWD (fun z => f z * c) (a * c) (b * c) w := by
  refine (HasFDerivAt.mul_const hf c).congr_fderiv ?_
  ext z; simp; all_goals ring
lemma HasWD.cderiv_comp {g : ℂ → ℂ} {a b w : ℂ} {p : ℂ → ℂ} {p' : ℂ}
    (hp : HasDerivAt p p' (g w)) (hg : HasWD g a b w) :
    HasWD (fun z => p (g z)) (p' * a) (p' * b) w := by
  refine (((hp.hasFDerivAt.restrictScalars ℝ).comp w hg)).congr_fderiv ?_
  ext z; simp; all_goals ring
lemma HasWD.inv {g : ℂ → ℂ} {a b w : ℂ} (hg : HasWD g a b w) (hgw : g w ≠ 0) :
    HasWD (fun z => (g z)⁻¹) (-a / (g w)^2) (-b / (g w)^2) w := by
  refine (HasWD.cderiv_comp (hasDerivAt_inv hgw) hg).congr ?_ ?_ <;> field_simp
lemma HasWD.div {f g : ℂ → ℂ} {a b c d w : ℂ} (hf : HasWD f a b w) (hg : HasWD g c d w)
    (hgw : g w ≠ 0) :
    HasWD (fun z => f z / g z)
      ((a * g w - f w * c) / (g w)^2) ((b * g w - f w * d) / (g w)^2) w := by
  have he : (fun z => f z / g z) = fun z => f z * (g z)⁻¹ := by funext z; rw [div_eq_mul_inv]
  rw [he]
  refine (HasWD.mul hf (hg.inv hgw)).congr ?_ ?_ <;> field_simp <;> ring

lemma laplacian_eq (f a b : ℂ → ℂ) (Ba Ab : ℂ) (w : ℂ)
    (hf : ∀ z, HasWD f (a z) (b z) z)
    (ha : ∃ Aa, HasWD a Aa Ba w) (hb : ∃ Bb, HasWD b Ab Bb w) :
    laplacian f w = 2 * Ba + 2 * Ab := by
  obtain ⟨Aa, ha⟩ := ha
  obtain ⟨Bb, hb⟩ := hb
  have hfd : ∀ z, fderiv ℝ f z = wlin (a z) (b z) := fun z => (hf z).fderiv
  have h1 : (fun z => fderiv ℝ f z 1) = fun z => a z + b z := by
    funext z; rw [hfd z]; simp
  have h2 : (fun z => fderiv ℝ f z I) = fun z => (a z - b z) * I := by
    funext z; rw [hfd z]; simp [Complex.conj_I]; ring
  rw [laplacian, h1, h2]
  have d1 : HasWD (fun z => a z + b z) (Aa + Ab) (Ba + Bb) w := ha.add hb
  have d2 : HasWD (fun z => (a z - b z) * I) ((Aa - Ab) * I) ((Ba - Bb) * I) w :=
    (ha.sub hb).mul_const I
  rw [d1.fderiv, d2.fderiv]
  simp only [wlin_apply, Complex.conj_I, map_one]
  linear_combination ((Aa - Ab) - (Ba - Bb)) * Complex.I_mul_I

/-! ### A family containing all three Gauss-map components

With `n = k - 1`, `P z = z ^ n` and `Q z = conj z ^ n`, we study
`Ffun n α β γ = (α P + β Q + γ (P Q - 1)) / (P Q + 1)`.  The three components `nu1, nu2, nu3`
are the parameter choices `(1, 1, 0)`, `(-I, I, 0)` and `(0, 0, 1)`.
`Afun`, `Bfun` are the Wirtinger derivatives `∂_z Ffun`, `∂_z̄ Ffun`, and `Cval = ∂_z ∂_z̄ Ffun`.
-/

/-- Denominator `|z|^{2n} + 1 = z ^ n * conj z ^ n + 1`. -/
def Dfun (n : ℕ) (z : ℂ) : ℂ := z ^ n * ((starRingEnd ℂ) z) ^ n + 1
/-- Numerator `α z^n + β conj z^n + γ (|z|^{2n} - 1)`. -/
def Nfun (n : ℕ) (al be ga : ℂ) (z : ℂ) : ℂ :=
  al * z ^ n + be * ((starRingEnd ℂ) z) ^ n + ga * (z ^ n * ((starRingEnd ℂ) z) ^ n - 1)
/-- The model family `Nfun / Dfun`. -/
def Ffun (n : ℕ) (al be ga : ℂ) (z : ℂ) : ℂ := Nfun n al be ga z / Dfun n z
/-- The Wirtinger derivative `∂_z (Ffun n α β γ)`. -/
def Afun (n : ℕ) (al be ga : ℂ) (z : ℂ) : ℂ :=
  ((n : ℂ) * z ^ (n-1)) * (al + 2*ga*((starRingEnd ℂ) z)^n - be * (((starRingEnd ℂ) z)^n)^2)
    / (Dfun n z)^2
/-- The Wirtinger derivative `∂_z̄ (Ffun n α β γ)`. -/
def Bfun (n : ℕ) (al be ga : ℂ) (z : ℂ) : ℂ :=
  ((n : ℂ) * ((starRingEnd ℂ) z) ^ (n-1)) * (be + 2*ga*(z^n) - al * ((z^n))^2) / (Dfun n z)^2
/-- The mixed second derivative `∂_z ∂_z̄ (Ffun n α β γ)`; the Laplacian is four times this. -/
def Cval (n : ℕ) (al be ga : ℂ) (w : ℂ) : ℂ :=
  ((n : ℂ)^2 * (w ^ (n-1) * ((starRingEnd ℂ) w) ^ (n-1))) *
    (2*ga*(1 - w^n*((starRingEnd ℂ) w)^n) - 2*al*w^n - 2*be*((starRingEnd ℂ) w)^n) / (Dfun n w)^3

lemma Dfun_ne_zero (n : ℕ) (z : ℂ) : Dfun n z ≠ 0 := by
  have h : Dfun n z = ((Complex.normSq z ^ n + 1 : ℝ) : ℂ) := by
    rw [Dfun, ← mul_pow, Complex.mul_conj]; push_cast; ring
  rw [h]
  simp only [ne_eq, Complex.ofReal_eq_zero]
  have h2 : (0:ℝ) ≤ Complex.normSq z ^ n := pow_nonneg (Complex.normSq_nonneg z) n
  linarith

lemma hasWD_Dfun (n : ℕ) (z : ℂ) :
    HasWD (Dfun n) ((n : ℂ) * z ^ (n-1) * ((starRingEnd ℂ) z) ^ n)
      ((n : ℂ) * ((starRingEnd ℂ) z) ^ (n-1) * z ^ n) z := by
  have h := ((hasWD_pow n z).mul (hasWD_conj_pow n z)).add (hasWD_const 1 z)
  refine (h.congr_fun ?_).congr ?_ ?_
  · funext u; simp [Dfun]
  · ring
  · ring

lemma hasWD_Nfun (n : ℕ) (al be ga : ℂ) (z : ℂ) :
    HasWD (Nfun n al be ga)
      ((al + ga * ((starRingEnd ℂ) z) ^ n) * ((n : ℂ) * z ^ (n-1)))
      ((be + ga * z ^ n) * ((n : ℂ) * ((starRingEnd ℂ) z) ^ (n-1))) z := by
  have h := (((hasWD_const al z).mul (hasWD_pow n z)).add
      ((hasWD_const be z).mul (hasWD_conj_pow n z))).add
      ((hasWD_const ga z).mul (((hasWD_pow n z).mul (hasWD_conj_pow n z)).sub (hasWD_const 1 z)))
  refine (h.congr_fun ?_).congr ?_ ?_
  · funext u; simp [Nfun]
  · ring
  · ring

lemma hasWD_Ffun (n : ℕ) (al be ga : ℂ) (z : ℂ) :
    HasWD (Ffun n al be ga) (Afun n al be ga z) (Bfun n al be ga z) z := by
  have h := (hasWD_Nfun n al be ga z).div (hasWD_Dfun n z) (Dfun_ne_zero n z)
  refine (h.congr_fun ?_).congr ?_ ?_
  · funext u; rw [Ffun]
  · rw [Afun]; simp only [Nfun, Dfun]; field_simp; ring
  · rw [Bfun]; simp only [Nfun, Dfun]; field_simp; ring

lemma hasWD_Dsq (n : ℕ) (z : ℂ) :
    HasWD (fun u => (Dfun n u)^2) (2 * Dfun n z * ((n : ℂ) * z ^ (n-1) * ((starRingEnd ℂ) z) ^ n))
      (2 * Dfun n z * ((n : ℂ) * ((starRingEnd ℂ) z) ^ (n-1) * z ^ n)) z := by
  have h := (hasWD_Dfun n z).mul (hasWD_Dfun n z)
  refine (h.congr_fun ?_).congr ?_ ?_
  · funext u; rw [sq]
  · ring
  · ring


lemma hasWD_Afun (n : ℕ) (al be ga : ℂ) (w : ℂ) :
    ∃ Aa, HasWD (Afun n al be ga) Aa (Cval n al be ga w) w := by
  have hq := hasWD_conj_pow n w
  have hnum := ((hasWD_const ((n:ℂ)) w).mul (hasWD_pow (n-1) w)).mul
    (((hasWD_const al w).add ((hasWD_const (2*ga) w).mul hq)).sub
      ((hasWD_const be w).mul (hq.mul hq)))
  have h := hnum.div (hasWD_Dsq n w) (pow_ne_zero 2 (Dfun_ne_zero n w))
  refine ⟨_, (h.congr_fun ?_).congr rfl ?_⟩
  · funext u; simp only [Afun]; ring_nf
  · rw [Cval]; simp only [Dfun]; field_simp; ring

lemma hasWD_Bfun (n : ℕ) (al be ga : ℂ) (w : ℂ) :
    ∃ Bb, HasWD (Bfun n al be ga) (Cval n al be ga w) Bb w := by
  have hp := hasWD_pow n w
  have hnum := ((hasWD_const ((n:ℂ)) w).mul (hasWD_conj_pow (n-1) w)).mul
    (((hasWD_const be w).add ((hasWD_const (2*ga) w).mul hp)).sub
      ((hasWD_const al w).mul (hp.mul hp)))
  have h := hnum.div (hasWD_Dsq n w) (pow_ne_zero 2 (Dfun_ne_zero n w))
  refine ⟨_, (h.congr_fun ?_).congr ?_ rfl⟩
  · funext u; simp only [Bfun]; ring_nf
  · rw [Cval]; simp only [Dfun]; field_simp; ring

lemma laplacian_Ffun (n : ℕ) (al be ga : ℂ) (w : ℂ) :
    laplacian (Ffun n al be ga) w = 4 * Cval n al be ga w := by
  have h := laplacian_eq (Ffun n al be ga) (Afun n al be ga) (Bfun n al be ga)
    (Cval n al be ga w) (Cval n al be ga w) w (hasWD_Ffun n al be ga)
    (hasWD_Afun n al be ga w) (hasWD_Bfun n al be ga w)
  rw [h]; ring

lemma jacobi_Ffun (n : ℕ) (al be ga : ℂ) (w : ℂ) :
    laplacian (Ffun n al be ga) w
      + (8 * (n:ℂ)^2 * (w ^ (n-1) * ((starRingEnd ℂ) w) ^ (n-1)) / (Dfun n w)^2)
        * Ffun n al be ga w = 0 := by
  rw [laplacian_Ffun, Cval, Ffun, Nfun]
  have hD := Dfun_ne_zero n w
  field_simp [Dfun]
  ring


/-! ### Matching the Gauss-map components with `Ffun` -/

lemma norm_pow_eq (m : ℕ) (w : ℂ) :
    ((‖w‖ : ℂ)) ^ (2 * m) = w ^ m * ((starRingEnd ℂ) w) ^ m := by
  have h : ((‖w‖ : ℂ)) ^ 2 = w * (starRingEnd ℂ) w := by
    rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.mul_conj]
  rw [pow_mul, h, mul_pow]

lemma potV_eq (k : ℕ) (hk : 2 ≤ k) (w : ℂ) :
    ((potV k w : ℝ) : ℂ)
      = 8 * ((k - 1 : ℕ) : ℂ) ^ 2 *
          (w ^ (k - 1 - 1) * ((starRingEnd ℂ) w) ^ (k - 1 - 1)) / (Dfun (k - 1) w) ^ 2 := by
  have hkc : ((k : ℂ) - 1) = ((k - 1 : ℕ) : ℂ) := by
    have : ((k - 1 : ℕ) : ℂ) = (k : ℂ) - 1 := by
      push_cast [Nat.cast_sub (show 1 ≤ k by omega)]; ring
    rw [this]
  simp only [potV, Dfun]
  rw [show 2 * k - 4 = 2 * (k - 1 - 1) by omega, show 2 * k - 2 = 2 * (k - 1) by omega]
  push_cast
  rw [norm_pow_eq, norm_pow_eq, hkc]

/-- The vertical-translation field solves the flat Jacobi equation for `k ≥ 2`. -/
theorem jacobi_nu3 (k : ℕ) (hk : 2 ≤ k) (w : ℂ) :
    laplacian (nu3 k) w + (potV k w : ℂ) * nu3 k w = 0 := by
  have hfun : nu3 k = Ffun (k - 1) 0 0 1 := by
    funext z
    simp only [nu3, Ffun, Nfun, Dfun, show 2 * k - 2 = 2 * (k - 1) by omega]
    push_cast
    rw [norm_pow_eq]
    ring
  rw [hfun, potV_eq k hk w, jacobi_Ffun]

/-- The first horizontal-translation field solves the flat Jacobi equation for `k ≥ 2`. -/
theorem jacobi_nu1 (k : ℕ) (hk : 2 ≤ k) (w : ℂ) :
    laplacian (nu1 k) w + (potV k w : ℂ) * nu1 k w = 0 := by
  have hfun : nu1 k = Ffun (k - 1) 1 1 0 := by
    funext z
    have hre : ((2 * (z ^ (k - 1)).re : ℝ) : ℂ)
        = z ^ (k - 1) + ((starRingEnd ℂ) z) ^ (k - 1) := by
      rw [← map_pow]
      exact (Complex.add_conj (z ^ (k - 1))).symm
    simp only [nu1, Ffun, Nfun, Dfun, show 2 * k - 2 = 2 * (k - 1) by omega]
    rw [Complex.ofReal_div, hre]
    push_cast
    rw [norm_pow_eq]
    ring
  rw [hfun, potV_eq k hk w, jacobi_Ffun]

/-- The second horizontal-translation field solves the flat Jacobi equation for `k ≥ 2`. -/
theorem jacobi_nu2 (k : ℕ) (hk : 2 ≤ k) (w : ℂ) :
    laplacian (nu2 k) w + (potV k w : ℂ) * nu2 k w = 0 := by
  have hfun : nu2 k = Ffun (k - 1) (-I) I 0 := by
    funext z
    have him : ((2 * (z ^ (k - 1)).im : ℝ) : ℂ)
        = -I * z ^ (k - 1) + I * ((starRingEnd ℂ) z) ^ (k - 1) := by
      rw [← map_pow]
      have h := Complex.sub_conj (z ^ (k - 1))
      linear_combination I * h + ((2 * (z ^ (k - 1)).im : ℝ) : ℂ) * Complex.I_mul_I
    simp only [nu2, Ffun, Nfun, Dfun, show 2 * k - 2 = 2 * (k - 1) by omega]
    rw [Complex.ofReal_div, him]
    push_cast
    rw [norm_pow_eq]
    ring
  rw [hfun, potV_eq k hk w, jacobi_Ffun]

/-! ### From the flat Jacobi equation to the geometric one

`laplacianG = ρ_k^{-2} · laplacian` and `|A_k|² = ρ_k^{-2} · potV` (`potential_integrand`), so on
the disk (where `ρ_k > 0`, the punctures missing it) the flat equation `laplacian u + potV·u = 0`
is equivalent to the geometric Jacobi equation `Δ_g u + |A|²u = 0` — the per-copy content of
`Surface.IsJacobiField`.  These lemmas concern the equation on each open-disk chart; they do not by
themselves establish seam compatibility, bounded-family membership or a nullity bound. -/

/-- Away from the punctures, `|A_k(w)|² · ρ_k(w)² = potV_k(w)` (the `f ≡ 1` case of `potential_integrand`). -/
lemma absA_sq_mul_rho_sq {k : ℕ} (hk : 2 ≤ k) {w : ℂ} (hw : w ∉ punctures k) :
    absA k w ^ 2 * rho k w ^ 2 = potV k w := by
  have h := potential_integrand hk (fun _ => (1 : ℂ)) hw
  simpa using h

/-- **Flat ⟹ geometric Jacobi equation on the disk.**  Any solution of the flat equation
`laplacian f + potV_k · f = 0` solves the geometric one `laplacianG f + |A_k|²·f = 0` there. -/
lemma laplacianG_add_absASq_of_flat {k : ℕ} (hk : 2 ≤ k) {f : ℂ → ℂ} {w : ℂ} (hw : w ∈ disk)
    (h : laplacian f w + (potV k w : ℂ) * f w = 0) :
    laplacianG k f w + ((absA k w ^ 2 : ℝ) : ℂ) * f w = 0 := by
  have hnp : w ∉ punctures k := punctures_notMem_disk (by omega) hw
  have hρ : (0 : ℝ) < rho k w := rho_pos (by omega) hnp
  have hρ2 : (rho k w ^ 2 : ℝ) ≠ 0 := by positivity
  have hV : (absA k w ^ 2 : ℝ) = (rho k w ^ 2)⁻¹ * potV k w := by
    field_simp
    linear_combination absA_sq_mul_rho_sq hk hnp
  have key : laplacianG k f w + ((absA k w ^ 2 : ℝ) : ℂ) * f w
      = (((rho k w ^ 2)⁻¹ : ℝ) : ℂ) * (laplacian f w + (potV k w : ℂ) * f w) := by
    rw [laplacianG, hV]
    push_cast
    ring
  rw [key, h, mul_zero]

/-- Vertical translation: `nu3` solves the geometric Jacobi equation on the disk. -/
theorem laplacianG_nu3 {k : ℕ} (hk : 2 ≤ k) {w : ℂ} (hw : w ∈ disk) :
    laplacianG k (nu3 k) w + ((absA k w ^ 2 : ℝ) : ℂ) * nu3 k w = 0 :=
  laplacianG_add_absASq_of_flat hk hw (jacobi_nu3 k hk w)

/-- First horizontal translation: `nu1` solves the geometric Jacobi equation on the disk. -/
theorem laplacianG_nu1 {k : ℕ} (hk : 2 ≤ k) {w : ℂ} (hw : w ∈ disk) :
    laplacianG k (nu1 k) w + ((absA k w ^ 2 : ℝ) : ℂ) * nu1 k w = 0 :=
  laplacianG_add_absASq_of_flat hk hw (jacobi_nu1 k hk w)

/-- Second horizontal translation: `nu2` solves the geometric Jacobi equation on the disk. -/
theorem laplacianG_nu2 {k : ℕ} (hk : 2 ≤ k) {w : ℂ} (hw : w ∈ disk) :
    laplacianG k (nu2 k) w + ((absA k w ^ 2 : ℝ) : ℂ) * nu2 k w = 0 :=
  laplacianG_add_absASq_of_flat hk hw (jacobi_nu2 k hk w)

end KsIndex.JacobiFields
