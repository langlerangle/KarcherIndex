module

public import KsIndexLean.KarcherInfinity
public import KsIndexLean.KarcherRealDifferential

@[expose] public section


/-!
# Symmetry transformations of the normalized Enneper–Weierstrass data

This module gives algebraic identities for the Gauss map, height differential,
Weierstrass coefficients and real differential under multiplication by roots of
unity, complex conjugation, and inversion combined with conjugation. The
inversion identities themselves are imported from `KarcherInfinity`.

For `k ≥ 1` and `a^(2k) = 1`, the real horizontal differential transforms by
multiplication by `a⁻¹`. Its vertical component is preserved when `a^k = 1`
and negated when `a^k = -1`. The seam reflection requires `k ≥ 2` and `w ≠ 0`.
Composing it with a half rotation gives the linear part of the screw symmetry:
horizontal rotation with the vertical differential fixed. Recovering the
vertical translation requires a separate integration constant.

These differential identities are ingredients for the integrated surface
symmetries; this module does not classify the full symmetry group.
-/
noncomputable section
namespace KsIndex.KarcherData

/-- Rotation building block (unconditional): `gauss k (a·w) = a^(k-1)·gauss k w`. -/
lemma gauss_mul (k : ℕ) (a w : ℂ) : gauss k (a * w) = a ^ (k - 1) * gauss k w := by
  simp [gauss, mul_pow]

/-- `etaTarget` is invariant under rotation by a `2k`-th root of unity (`a^(2k) = 1`). -/
lemma etaTarget_rot {k : ℕ} {a : ℂ} (ha : a ^ (2 * k) = 1) (w : ℂ) :
    etaTarget k (a * w) = etaTarget k w := by
  unfold etaTarget
  rw [mul_pow, ha, one_mul]

/-- Conjugation: `gauss k (conj w) = conj (gauss k w)`. -/
lemma gauss_conj (k : ℕ) (w : ℂ) :
    gauss k (starRingEnd ℂ w) = starRingEnd ℂ (gauss k w) := by
  simp [gauss, map_pow]

/-- Conjugation: `etaTarget k (conj w) = conj (etaTarget k w)` (`k` real). -/
lemma etaTarget_conj (k : ℕ) (w : ℂ) :
    etaTarget k (starRingEnd ℂ w) = starRingEnd ℂ (etaTarget k w) := by
  simp [etaTarget, map_div₀, map_add, map_pow, map_one, map_natCast]

/-! ### Coefficient conjugation (the `refl_{y=0}` building blocks).

`conj` acts on the Weierstrass data componentwise; the `i` in `phi2` flips the sign, so the
coefficient triple transforms as `(coeff1, -coeff2, coeff3)` under `conj∘conj` — i.e. the ℝ³
isometry `diag(1,-1,1)` (`refl_{y=0}`). These also feed the `refl_{z=0}` composition
(inversion `(φ1,-φ2,-φ3)` ∘ conjugation `(φ1,-φ2,φ3)` = `diag(1,1,-1)`). -/

/-- `coeff1 (conj w) = conj (coeff1 w)`. -/
lemma coeff1_conj (k : ℕ) (w : ℂ) :
    coeff1 k (starRingEnd ℂ w) = starRingEnd ℂ (coeff1 k w) := by
  simp only [coeff1, Weierstrass.phi1, gauss_conj, etaTarget_conj, map_mul, map_sub, map_one,
    map_pow]

/-- `coeff2 (conj w) = -conj (coeff2 w)` — the `i` in `phi2` flips the sign. -/
lemma coeff2_conj (k : ℕ) (w : ℂ) :
    coeff2 k (starRingEnd ℂ w) = -starRingEnd ℂ (coeff2 k w) := by
  simp only [coeff2, Weierstrass.phi2, gauss_conj, etaTarget_conj, map_mul, map_add, map_one,
    map_pow, Complex.conj_I]
  ring

/-- `coeff3 (conj w) = conj (coeff3 w)`. -/
lemma coeff3_conj (k : ℕ) (w : ℂ) :
    coeff3 k (starRingEnd ℂ w) = starRingEnd ℂ (coeff3 k w) := by
  simp only [coeff3, Weierstrass.phi3, gauss_conj, etaTarget_conj, map_mul, map_ofNat]

/-! ### `refl_{z=0}` seam-reflection pullback (`w ↦ 1/conj w`), by composition.

The seam reflection `σ(w) = 1/conj w = (conj w)⁻¹` factors as holomorphic inversion ∘ conjugation.
Composing `coeff*_inv_pullback` (KarcherInfinity, the `(φ1,-φ2,-φ3)` inversion with chart factor
`-(·)²`) at `conj w` with `coeff*_conj` gives the pulled-back coefficients as `(conj φ1, conj φ2,
-conj φ3)` — i.e. the ℝ³ isometry `diag(1,1,-1) = refl_{z=0}` after the conjugation of the
anti-holomorphic pullback. The sign pattern: `(+, +, -)` on the conjugates (the two `-1`s from the
inversion on `φ2,φ3` combine with the `-1` from `conj` on `φ2` to give `+` on `φ2`, `-` on `φ3`). -/

private lemma conj_ne_zero {w : ℂ} (hw : w ≠ 0) : starRingEnd ℂ w ≠ 0 := by
  simpa using hw

/-- `coeff1` under the seam reflection `w ↦ (conj w)⁻¹`, with the inversion chart factor. -/
lemma coeff1_refl_z_pullback {k : ℕ} (hk : 2 ≤ k) {w : ℂ} (hw : w ≠ 0) :
    coeff1 k (starRingEnd ℂ w)⁻¹ * (-((starRingEnd ℂ w)⁻¹) ^ 2)
      = starRingEnd ℂ (coeff1 k w) := by
  rw [coeff1_inv_pullback hk (conj_ne_zero hw), coeff1_conj]

/-- `coeff2` under the seam reflection: the inversion `-φ2` and `conj`'s `-φ2` combine to `+conj φ2`. -/
lemma coeff2_refl_z_pullback {k : ℕ} (hk : 2 ≤ k) {w : ℂ} (hw : w ≠ 0) :
    coeff2 k (starRingEnd ℂ w)⁻¹ * (-((starRingEnd ℂ w)⁻¹) ^ 2)
      = starRingEnd ℂ (coeff2 k w) := by
  rw [coeff2_inv_pullback hk (conj_ne_zero hw), coeff2_conj]; ring

/-- `coeff3` under the seam reflection: `-conj φ3` (the `diag(1,1,-1)` height reflection). -/
lemma coeff3_refl_z_pullback {k : ℕ} (hk : 2 ≤ k) {w : ℂ} (hw : w ≠ 0) :
    coeff3 k (starRingEnd ℂ w)⁻¹ * (-((starRingEnd ℂ w)⁻¹) ^ 2)
      = -starRingEnd ℂ (coeff3 k w) := by
  rw [coeff3_inv_pullback hk (conj_ne_zero hw), coeff3_conj]

/-! ### Rotation equivariance via the eigen-combinations `A=φ1+iφ2`, `B=φ1-iφ2`, `C=φ3`.

The individual `coeff` do not scale under rotation, but `A,B,C` diagonalize it:
`A = -2g²h`, `B = 2h`, `C = 2gh`. Under `w ↦ a·w` (with `a^(2k)=1`): `g ↦ a^(k-1)g`, `h ↦ h`, so
`A ↦ (a^(k-1))²A`, `B ↦ B`, `C ↦ a^(k-1)C`. Folding the chart derivative `a` and `a^k = 1` (paper's
`a = e^{-2πi/k}`) gives the ℝ³ rotation eigenvalues `(ζ, ζ⁻¹, 1)` on `(A,B,C)` with `ζ = a^{-1}`. -/

/-- Closed form `A = φ1 + iφ2 = -2 g² h`. -/
lemma coeff_combo_A (k : ℕ) (w : ℂ) :
    coeff1 k w + Complex.I * coeff2 k w = -2 * (gauss k w) ^ 2 * etaTarget k w := by
  simp only [coeff1, coeff2, Weierstrass.phi1, Weierstrass.phi2]
  linear_combination (1 + (gauss k w) ^ 2) * etaTarget k w * Complex.I_mul_I

/-- Closed form `B = φ1 - iφ2 = 2 h`. -/
lemma coeff_combo_B (k : ℕ) (w : ℂ) :
    coeff1 k w - Complex.I * coeff2 k w = 2 * etaTarget k w := by
  simp only [coeff1, coeff2, Weierstrass.phi1, Weierstrass.phi2]
  linear_combination (-(1 + (gauss k w) ^ 2) * etaTarget k w) * Complex.I_mul_I

/-- Rotation on `A`: `A(a·w) = (a^(k-1))²·A(w)` for `a^(2k)=1`. -/
lemma coeff_combo_A_rot {k : ℕ} {a : ℂ} (ha : a ^ (2 * k) = 1) (w : ℂ) :
    coeff1 k (a * w) + Complex.I * coeff2 k (a * w)
      = (a ^ (k - 1)) ^ 2 * (coeff1 k w + Complex.I * coeff2 k w) := by
  rw [coeff_combo_A, coeff_combo_A, gauss_mul, etaTarget_rot ha]; ring

/-- Rotation on `B`: `B(a·w) = B(w)` for `a^(2k)=1`. -/
lemma coeff_combo_B_rot {k : ℕ} {a : ℂ} (ha : a ^ (2 * k) = 1) (w : ℂ) :
    coeff1 k (a * w) - Complex.I * coeff2 k (a * w) = coeff1 k w - Complex.I * coeff2 k w := by
  rw [coeff_combo_B, coeff_combo_B, etaTarget_rot ha]

/-- Rotation on `C = φ3`: `C(a·w) = a^(k-1)·C(w)` for `a^(2k)=1`. -/
lemma coeff3_rot {k : ℕ} {a : ℂ} (ha : a ^ (2 * k) = 1) (w : ℂ) :
    coeff3 k (a * w) = a ^ (k - 1) * coeff3 k w := by
  simp only [coeff3, Weierstrass.phi3, gauss_mul, etaTarget_rot ha]; ring

/-! ### Differential-level equivariance (lifting the coeff equivariance to `ewRealDifferential`).

`refl_{y=0}`: the anti-holomorphic deck `w ↦ conj w` acts on the real differential by `diag(1,-1,1)`,
evaluated on `conj d` (the anti-holomorphic chart derivative). This lifts `coeff1/2/3_conj` through
`realCoeffLinear a d = (d·a).re`, using `conj d · conj a = conj (d·a)` and `(conj z).re = z.re`. -/

/-- `refl_{y=0}` on the EW real differential: `dX(conj w)(conj d) = diag(1,-1,1)·dX(w)(d)`. -/
lemma ewRealDifferential_conj {k : ℕ} (w d : ℂ) :
    ewRealDifferential k (starRingEnd ℂ w) (starRingEnd ℂ d)
      = ((ewRealDifferential k w d).1, -(ewRealDifferential k w d).2.1,
          (ewRealDifferential k w d).2.2) := by
  simp only [ewRealDifferential, ContinuousLinearMap.prod_apply, realCoeffLinear_apply,
    coeff1_conj, coeff2_conj, coeff3_conj, mul_neg, ← map_mul, Complex.conj_re, Complex.neg_re]

/-- `refl_{z=0}` on the EW real differential: with the inversion chart factor,
`dX(1/conj w)(-conj d / (conj w)²) = (dx, dy, -dz)` where `(dx,dy,dz) = dX(w)(d)`; needs `w ≠ 0`. -/
lemma ewRealDifferential_refl_z {k : ℕ} (hk : 2 ≤ k) {w : ℂ} (hw : w ≠ 0) (d : ℂ) :
    ewRealDifferential k (starRingEnd ℂ w)⁻¹ (-(starRingEnd ℂ d) / (starRingEnd ℂ w) ^ 2)
      = ((ewRealDifferential k w d).1, (ewRealDifferential k w d).2.1,
          -(ewRealDifferential k w d).2.2) := by
  have hδ : -(starRingEnd ℂ d) / (starRingEnd ℂ w) ^ 2
      = -(starRingEnd ℂ d) * ((starRingEnd ℂ w)⁻¹) ^ 2 := by
    rw [div_eq_mul_inv, ← inv_pow]
  have c1 : -(starRingEnd ℂ d) * ((starRingEnd ℂ w)⁻¹) ^ 2 * coeff1 k (starRingEnd ℂ w)⁻¹
      = starRingEnd ℂ (d * coeff1 k w) := by
    have h : ((starRingEnd ℂ w)⁻¹) ^ 2 * coeff1 k (starRingEnd ℂ w)⁻¹
        = -starRingEnd ℂ (coeff1 k w) := by linear_combination -coeff1_refl_z_pullback hk hw
    rw [mul_assoc, h, map_mul]; ring
  have c2 : -(starRingEnd ℂ d) * ((starRingEnd ℂ w)⁻¹) ^ 2 * coeff2 k (starRingEnd ℂ w)⁻¹
      = starRingEnd ℂ (d * coeff2 k w) := by
    have h : ((starRingEnd ℂ w)⁻¹) ^ 2 * coeff2 k (starRingEnd ℂ w)⁻¹
        = -starRingEnd ℂ (coeff2 k w) := by linear_combination -coeff2_refl_z_pullback hk hw
    rw [mul_assoc, h, map_mul]; ring
  have c3 : -(starRingEnd ℂ d) * ((starRingEnd ℂ w)⁻¹) ^ 2 * coeff3 k (starRingEnd ℂ w)⁻¹
      = -starRingEnd ℂ (d * coeff3 k w) := by
    have h : ((starRingEnd ℂ w)⁻¹) ^ 2 * coeff3 k (starRingEnd ℂ w)⁻¹
        = starRingEnd ℂ (coeff3 k w) := by linear_combination -coeff3_refl_z_pullback hk hw
    rw [mul_assoc, h, map_mul]; ring
  simp only [ewRealDifferential, ContinuousLinearMap.prod_apply, realCoeffLinear_apply, hδ,
    Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · rw [c1, Complex.conj_re]
  · rw [c2, Complex.conj_re]
  · rw [c3, Complex.neg_re, Complex.conj_re]

/-! ### Rotation differential equivariance.

For `k ≥ 1`, including the chart derivative makes `d·C` scale by `a^k`. Taking real
parts preserves height when `a^k=1` and reverses it when `a^k=-1`. Horizontal: `x+iy = (d·A + conj(d·B))/2` (real-part
decomposition), and under `w↦a·w` with `a^(2k)=1`, `|a|=1`: `A↦(a^(k-1))²A`, `B↦B`, chart factor `a`,
giving `(x+iy) ↦ a⁻¹·(x+iy)` (the ambient phase `c = a⁻¹`). -/

lemma mul_pow_pred {k : ℕ} (hk : 1 ≤ k) (a : ℂ) : a * a ^ (k - 1) = a ^ k := by
  rw [← pow_succ', show k - 1 + 1 = k from by omega]

/-- Height under full rotation (`a^k=1`): preserved. -/
lemma ewRealDifferential_rot_height {k : ℕ} (hk : 1 ≤ k) {a : ℂ} (ha : a ^ k = 1) (w d : ℂ) :
    (ewRealDifferential k (a * w) (a * d)).2.2 = (ewRealDifferential k w d).2.2 := by
  have h2k : a ^ (2 * k) = 1 := by rw [two_mul, pow_add, ha, one_mul]
  simp only [ewRealDifferential, ContinuousLinearMap.prod_apply, realCoeffLinear_apply, coeff3_rot h2k]
  rw [show a * d * (a ^ (k - 1) * coeff3 k w) = (a * a ^ (k - 1)) * (d * coeff3 k w) from by ring,
    mul_pow_pred hk, ha, one_mul]

/-- Height under half rotation (`a^k=-1`): flipped. -/
lemma ewRealDifferential_half_rot_height {k : ℕ} (hk : 1 ≤ k) {a : ℂ} (ha : a ^ k = -1) (w d : ℂ) :
    (ewRealDifferential k (a * w) (a * d)).2.2 = -(ewRealDifferential k w d).2.2 := by
  have h2k : a ^ (2 * k) = 1 := by rw [two_mul, pow_add, ha]; ring
  simp only [ewRealDifferential, ContinuousLinearMap.prod_apply, realCoeffLinear_apply, coeff3_rot h2k]
  rw [show a * d * (a ^ (k - 1) * coeff3 k w) = (a * a ^ (k - 1)) * (d * coeff3 k w) from by ring,
    mul_pow_pred hk, ha, neg_one_mul, Complex.neg_re]

/-! ### Compatibility with the projection to `PeriodTarget`.

`projectPeriod : ℝ×ℝ×ℝ → ℝ×ℝ×AddCircle(2π)` touches only the vertical coordinate, so the horizontal
rotation (fixes `z`) and the `refl_z` vertical sign (`z↦-z`, descending to negation on `AddCircle`)
both commute with it — the foundation for `descendedIntegral` equivariance under the surface symmetries. -/

/-- Horizontal complex multiplication commutes with `projectPeriod`; for unit `c` this is rotation. -/
lemma projectPeriod_horiz_rot (c : ℂ) (x y z : ℝ) :
    projectPeriod (c.re * x - c.im * y, c.im * x + c.re * y, z)
      = (c.re * x - c.im * y, c.im * x + c.re * y, (projectPeriod (x, y, z)).2.2) := by
  simp [projectPeriod]

/-- `refl_z` (vertical sign) descends to negation on the `AddCircle` factor. -/
lemma projectPeriod_vert_neg (x y z : ℝ) :
    projectPeriod (x, y, -z) = (x, y, -(projectPeriod (x, y, z)).2.2) := by
  simp [projectPeriod]

/-- Horizontal decomposition: `Re(d·u) + i·Re(d·v) = (d(u+iv) + conj(d(u-iv)))/2`, scaled by 2. -/
lemma two_horiz_decomp (d u v : ℂ) :
    2 * (((d * u).re : ℂ) + ((d * v).re : ℂ) * Complex.I)
      = d * (u + Complex.I * v) + starRingEnd ℂ (d * (u - Complex.I * v)) := by
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.conj_re, Complex.conj_im] <;> ring

/-- Horizontal part under rotation (`a^(2k)=1`, covering full `a^k=1` and half `a^k=-1`):
`(x+iy) ↦ a⁻¹·(x+iy)` (ambient phase `c=a⁻¹`). The height component is handled separately
(`ewRealDifferential_rot_height` / `_half_rot_height`). -/
lemma ewRealDifferential_rot_horiz {k : ℕ} (hk : 1 ≤ k) {a : ℂ} (h2k : a ^ (2 * k) = 1) (w d : ℂ) :
    ((ewRealDifferential k (a * w) (a * d)).1 : ℂ)
        + ((ewRealDifferential k (a * w) (a * d)).2.1 : ℂ) * Complex.I
      = a⁻¹ * (((ewRealDifferential k w d).1 : ℂ)
        + ((ewRealDifferential k w d).2.1 : ℂ) * Complex.I) := by
  have hane : a ≠ 0 := by
    rintro rfl; rw [zero_pow (by omega : 2 * k ≠ 0)] at h2k; exact zero_ne_one h2k
  have hnorm : ‖a‖ = 1 := by
    have hn : ‖a‖ ^ (2 * k) = 1 := by rw [← norm_pow, h2k, norm_one]
    rcases lt_trichotomy ‖a‖ 1 with h | h | h
    · exact absurd hn (ne_of_lt (pow_lt_one₀ (norm_nonneg a) h (by omega)))
    · exact h
    · exact absurd hn (ne_of_gt (one_lt_pow₀ h (by omega)))
  have hconja : starRingEnd ℂ a = a⁻¹ := (Complex.inv_eq_conj hnorm).symm
  have ha1 : a * (a ^ (k - 1)) ^ 2 = a⁻¹ := by
    have key : a * (a * (a ^ (k - 1)) ^ 2) = 1 := by
      rw [show a * (a * (a ^ (k - 1)) ^ 2) = (a * a ^ (k - 1)) ^ 2 from by ring, mul_pow_pred hk,
        ← pow_mul, mul_comm k 2, h2k]
    rw [inv_eq_one_div, eq_div_iff hane]
    linear_combination key
  have hL := two_horiz_decomp (a * d) (coeff1 k (a * w)) (coeff2 k (a * w))
  rw [coeff_combo_A_rot h2k, coeff_combo_B_rot h2k] at hL
  have hR := two_horiz_decomp d (coeff1 k w) (coeff2 k w)
  simp only [ewRealDifferential, ContinuousLinearMap.prod_apply, realCoeffLinear_apply]
  refine mul_left_cancel₀ (two_ne_zero) ?_
  rw [hL, show (2 : ℂ) * (a⁻¹ * (((d * coeff1 k w).re : ℂ) + ((d * coeff2 k w).re : ℂ) * Complex.I))
      = a⁻¹ * (2 * (((d * coeff1 k w).re : ℂ) + ((d * coeff2 k w).re : ℂ) * Complex.I)) from by ring,
    hR, show a * d * ((a ^ (k - 1)) ^ 2 * (coeff1 k w + Complex.I * coeff2 k w))
      = (a * (a ^ (k - 1)) ^ 2) * (d * (coeff1 k w + Complex.I * coeff2 k w)) from by ring, ha1,
    show a * d * (coeff1 k w - Complex.I * coeff2 k w) = a * (d * (coeff1 k w - Complex.I * coeff2 k w))
      from by ring, map_mul, hconja]
  ring

/-! ### Screw differential equivariance (`rot_z^{π/k} trans_z^π`, deck `w ↦ β/w̄`, `β=e^{-iπ/k}`).

`screw = rot_β ∘ σ` with `σ = refl_z` (seam reflection) and `β^k = -1`. Composing the two:
`σ` flips height, `rot_β` (half-rotation) flips height again ⟹ the two CANCEL, leaving the LINEAR part
= horizontal rotation by `β⁻¹`, **height fixed**. The affine `z↦z+π` is a separate
integrated constant (NOT from this derivative calculation). -/

/-- Screw horizontal: rotates `x+iy` by `β⁻¹` (`β^k=-1`), via `rot_horiz(β) ∘ refl_z`. -/
lemma ewRealDifferential_screw_horiz {k : ℕ} (hk : 2 ≤ k) {β : ℂ} (hβk : β ^ k = -1) {w : ℂ}
    (hw : w ≠ 0) (d : ℂ) :
    ((ewRealDifferential k (β * (starRingEnd ℂ w)⁻¹)
          (β * (-(starRingEnd ℂ d) / (starRingEnd ℂ w) ^ 2))).1 : ℂ)
        + ((ewRealDifferential k (β * (starRingEnd ℂ w)⁻¹)
          (β * (-(starRingEnd ℂ d) / (starRingEnd ℂ w) ^ 2))).2.1 : ℂ) * Complex.I
      = β⁻¹ * (((ewRealDifferential k w d).1 : ℂ) + ((ewRealDifferential k w d).2.1 : ℂ) * Complex.I) := by
  have hβ2k : β ^ (2 * k) = 1 := by rw [two_mul, pow_add, hβk]; ring
  rw [ewRealDifferential_rot_horiz (by omega) hβ2k ((starRingEnd ℂ w)⁻¹)
      (-(starRingEnd ℂ d) / (starRingEnd ℂ w) ^ 2), ewRealDifferential_refl_z hk hw d]

/-- Screw height: FIXED (the two height reflections cancel), via `half_rot_height(β) ∘ refl_z`. -/
lemma ewRealDifferential_screw_height {k : ℕ} (hk : 2 ≤ k) {β : ℂ} (hβk : β ^ k = -1) {w : ℂ}
    (hw : w ≠ 0) (d : ℂ) :
    (ewRealDifferential k (β * (starRingEnd ℂ w)⁻¹)
        (β * (-(starRingEnd ℂ d) / (starRingEnd ℂ w) ^ 2))).2.2 = (ewRealDifferential k w d).2.2 := by
  rw [ewRealDifferential_half_rot_height (by omega) hβk ((starRingEnd ℂ w)⁻¹)
      (-(starRingEnd ℂ d) / (starRingEnd ℂ w) ^ 2), ewRealDifferential_refl_z hk hw d, neg_neg]

end KsIndex.KarcherData
