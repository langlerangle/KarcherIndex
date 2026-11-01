module

public import KsIndexLean.KarcherResidues

@[expose] public section


/-!
# The normalized EW differential in the infinity chart

For v = 1/w the pulled-back one-form is (coeff1, -coeff2, -coeff3),
including the factor dw/dv = -1/v². These rational functions extend at
v=0 with positive conformal metric for k ≥ 2. This module establishes the
differential identities. `KarcherInfinityPrimitive` constructs a local immersion,
and `KarcherInfinityIdentification` identifies it with the descended integral
on the punctured overlap, up to a constant in the period quotient.
-/
noncomputable section
namespace KsIndex.KarcherData

lemma gauss_inv (k : ℕ) (v : ℂ) : gauss k v⁻¹ = (gauss k v)⁻¹ := by
  simp [gauss, inv_pow]

lemma etaTarget_inv {k : ℕ} {v : ℂ} (hv : v ≠ 0) :
    etaTarget k v⁻¹ = v ^ (2 * k) * etaTarget k v := by
  have hpow := pow_ne_zero (2 * k) hv
  have he : 1 + (v ^ (2 * k))⁻¹ = (1 + v ^ (2 * k)) / v ^ (2 * k) := by
    field_simp
    ring
  unfold etaTarget
  rw [inv_pow, he, div_div_eq_mul_div]
  ring

/-- The scalar differential coefficient includes the inversion derivative. -/
lemma etaTarget_inv_pullback {k : ℕ} (hk : 2 ≤ k) {v : ℂ}
    (hv : v ≠ 0) :
    etaTarget k v⁻¹ * (-(v⁻¹) ^ 2) = -(gauss k v) ^ 2 * etaTarget k v := by
  rw [etaTarget_inv hv]
  have he : v ^ (2 * k) = (gauss k v) ^ 2 * v ^ 2 := by
    unfold gauss
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [he]
  field_simp

/-- The finite-chart first component is also the extended infinity component. -/
lemma coeff1_inv_pullback {k : ℕ} (hk : 2 ≤ k) {v : ℂ}
    (hv : v ≠ 0) :
    coeff1 k v⁻¹ * (-(v⁻¹) ^ 2) = coeff1 k v := by
  have hg : gauss k v ≠ 0 := pow_ne_zero _ hv
  simp only [coeff1, Weierstrass.phi1, mul_assoc, etaTarget_inv_pullback hk hv,
    gauss_inv]
  field_simp
  ring

lemma coeff2_inv_pullback {k : ℕ} (hk : 2 ≤ k) {v : ℂ}
    (hv : v ≠ 0) :
    coeff2 k v⁻¹ * (-(v⁻¹) ^ 2) = -coeff2 k v := by
  have hg : gauss k v ≠ 0 := pow_ne_zero _ hv
  simp only [coeff2, Weierstrass.phi2, mul_assoc, etaTarget_inv_pullback hk hv,
    gauss_inv]
  field_simp
  ring

lemma coeff3_inv_pullback {k : ℕ} (hk : 2 ≤ k) {v : ℂ}
    (hv : v ≠ 0) :
    coeff3 k v⁻¹ * (-(v⁻¹) ^ 2) = -coeff3 k v := by
  have hg : gauss k v ≠ 0 := pow_ne_zero _ hv
  simp only [coeff3, Weierstrass.phi3, mul_assoc, etaTarget_inv_pullback hk hv,
    gauss_inv]
  field_simp

/-- Extended coefficients, not the totalized singular expression at v=0. -/
def infinityCoeff (k : ℕ) (v : ℂ) : ℂ × ℂ × ℂ :=
  (coeff1 k v, -coeff2 k v, -coeff3 k v)

lemma differentiableAt_infinityCoeff {k : ℕ} {v : ℂ}
    (hp : v ∉ Surface.punctures k) : DifferentiableAt ℂ (infinityCoeff k) v := by
  exact (differentiableAt_coeff1 hp).prodMk
    ((differentiableAt_coeff2 hp).neg.prodMk (differentiableAt_coeff3 hp).neg)

lemma infinityCoeff_zero {k : ℕ} (hk : 2 ≤ k) :
    infinityCoeff k 0 = ((k : ℂ), -Complex.I * k, 0) := by
  simp [infinityCoeff, coeff1, coeff2, coeff3, gauss, etaTarget,
    Weierstrass.phi1, Weierstrass.phi2, Weierstrass.phi3,
    show k - 1 ≠ 0 by omega, show 2 * k ≠ 0 by omega]

/-- The coordinate derivative whose factor occurs in all three transitions. -/
lemma hasDerivAt_chartInversion {v : ℂ} (hv : v ≠ 0) :
    HasDerivAt (fun z : ℂ => z⁻¹) (-(v⁻¹) ^ 2) v := by
  simpa only [inv_pow] using hasDerivAt_inv hv

lemma differentiableAt_infinityCoeff_zero {k : ℕ} (hk : 2 ≤ k) :
    DifferentiableAt ℂ (infinityCoeff k) 0 := by
  apply differentiableAt_infinityCoeff
  simp [Surface.punctures, show 2 * k ≠ 0 by omega]

lemma infinityCoeff_null (k : ℕ) (v : ℂ) :
    (infinityCoeff k v).1 ^ 2 + (infinityCoeff k v).2.1 ^ 2 +
      (infinityCoeff k v).2.2 ^ 2 = 0 := by
  simpa [infinityCoeff, coeff1, coeff2, coeff3] using
    Weierstrass.weierstrass_null (gauss k v) (etaTarget k v)

lemma infinity_real_metric_eq_rho_sq {k : ℕ} (hk : 2 ≤ k) (v : ℂ) :
    Weierstrass.realSq (infinityCoeff k v).1
      (infinityCoeff k v).2.1 (infinityCoeff k v).2.2 = Surface.rho k v ^ 2 := by
  simpa [infinityCoeff, Weierstrass.realSq, coeff1, coeff2, coeff3] using
    real_metric_eq_rho_sq hk v

lemma infinity_equal_lengths (k : ℕ) (v : ℂ) :
    Weierstrass.realSq (infinityCoeff k v).1
      (infinityCoeff k v).2.1 (infinityCoeff k v).2.2 =
    Weierstrass.imagSq (infinityCoeff k v).1
      (infinityCoeff k v).2.1 (infinityCoeff k v).2.2 :=
  Weierstrass.null_equal_lengths (infinityCoeff_null k v)

lemma infinity_orthogonal (k : ℕ) (v : ℂ) :
    Weierstrass.realImagDot (infinityCoeff k v).1
      (infinityCoeff k v).2.1 (infinityCoeff k v).2.2 = 0 :=
  Weierstrass.null_orthogonal (infinityCoeff_null k v)

/-- In particular infinity is a regular point of the differential data. -/
lemma infinity_metric_pos {k : ℕ} (hk : 2 ≤ k) {v : ℂ}
    (hp : v ∉ Surface.punctures k) :
    0 < Weierstrass.realSq (infinityCoeff k v).1
      (infinityCoeff k v).2.1 (infinityCoeff k v).2.2 := by
  have he : Weierstrass.realSq (infinityCoeff k v).1
      (infinityCoeff k v).2.1 (infinityCoeff k v).2.2 =
      Weierstrass.realSq (coeff1 k v) (coeff2 k v) (coeff3 k v) := by
    simp [infinityCoeff, Weierstrass.realSq]
  rw [he]
  exact Weierstrass.weierstrass_metric_pos _ _ (etaTarget_ne_zero hk hp)

end KsIndex.KarcherData
