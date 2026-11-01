module

public import KsIndexLean.KarcherSecondFundamental
public import KsIndexLean.SphericalCoordinates

@[expose] public section


/-! The oriented normal of the actual EW representatives agrees with the
paper's north-pole stereographic convention. -/
noncomputable section
namespace KsIndex.KarcherData

/-- Convert ambient triples to the existing Euclidean spherical-model carrier. -/
def tripleToEuclidean (p : AmbientTriple) : Spherical.Ambient :=
  WithLp.toLp 2 ![p.1, p.2.1, p.2.2]

/-- The paper's inverse stereographic map, expressed in ambient triples. -/
def stereoNormal (g : ℂ) : AmbientTriple :=
  (2 * g.re / (1 + ‖g‖ ^ 2), 2 * g.im / (1 + ‖g‖ ^ 2),
    (‖g‖ ^ 2 - 1) / (1 + ‖g‖ ^ 2))

lemma continuous_stereoNormal : Continuous stereoNormal := by
  unfold stereoNormal
  fun_prop (disch := intros; positivity)

lemma tripleToEuclidean_stereoNormal (g : ℂ) :
    tripleToEuclidean (stereoNormal g) = Spherical.stereoPoint g := rfl

lemma stereoCoord_stereoNormal (g : ℂ) :
    Spherical.stereoCoord (tripleToEuclidean (stereoNormal g)) = g :=
  Spherical.stereoCoord_stereoPoint g

lemma weierstrass_cross (g h : ℂ) :
    euclideanCross
      ((Weierstrass.phi1 g h).re, (Weierstrass.phi2 g h).re, (Weierstrass.phi3 g h).re)
      (-(Weierstrass.phi1 g h).im, -(Weierstrass.phi2 g h).im, -(Weierstrass.phi3 g h).im) =
    (‖h‖ ^ 2 * (1 + ‖g‖ ^ 2)) • (2 * g.re, 2 * g.im, ‖g‖ ^ 2 - 1) := by
  simp only [Complex.sq_norm, Complex.normSq_apply]
  ext <;> simp [euclideanCross, Weierstrass.phi1, Weierstrass.phi2, Weierstrass.phi3,
    pow_two, Complex.mul_re, Complex.mul_im] <;> ring

lemma ew_differential_cross (k : ℕ) (w : ℂ) :
    euclideanCross (ewRealDifferential k w 1) (ewRealDifferential k w Complex.I) =
    (‖etaTarget k w‖ ^ 2 * (1 + ‖gauss k w‖ ^ 2)) •
      (2 * (gauss k w).re, 2 * (gauss k w).im, ‖gauss k w‖ ^ 2 - 1) := by
  convert weierstrass_cross (gauss k w) (etaTarget k w) using 1
  simp [ewRealDifferential, realCoeffLinear_apply, coeff1, coeff2, coeff3]

lemma chartUnitNormal_eq_inv_conformal {X : ℂ → AmbientTriple} {w : ℂ} {q : ℝ}
    (hq : 0 < q)
    (hm : ∀ d : ℂ, euclideanSq (fderiv ℝ X w d) = q * ‖d‖ ^ 2) :
    chartUnitNormal X w = q⁻¹ •
      euclideanCross (fderiv ℝ X w 1) (fderiv ℝ X w Complex.I) := by
  obtain ⟨_, hF, _⟩ := metric_coefficients_of_conformal hm
  have h1 : euclideanSq (fderiv ℝ X w 1) = q := by simpa using hm 1
  have hi : euclideanSq (fderiv ℝ X w Complex.I) = q := by simpa using hm Complex.I
  have hc : euclideanSq (euclideanCross (fderiv ℝ X w 1) (fderiv ℝ X w Complex.I)) = q ^ 2 := by
    rw [euclideanCross_sq, h1, hi, hF]
    ring
  unfold chartUnitNormal
  rw [hc, Real.sqrt_sq hq.le]

/-- The positive-coordinate normal of an actual finite EW representative is
exactly the inverse stereographic image of g = w^(k-1), with no sign choice left. -/
theorem ew_chartUnitNormal_eq_stereoNormal {k : ℕ} (hk : 2 ≤ k)
    {X : ℂ → AmbientTriple} {w : ℂ} (hw : w ∉ Surface.punctures k)
    (hd : HasFDerivAt X (ewRealDifferential k w) w) :
    chartUnitNormal X w = stereoNormal (gauss k w) := by
  have hm : ∀ d : ℂ, euclideanSq (fderiv ℝ X w d) = Surface.rho k w ^ 2 * ‖d‖ ^ 2 := by
    intro d
    rw [hd.fderiv, ewRealDifferential_metric hk]
  rw [chartUnitNormal_eq_inv_conformal (rho_sq_pos hk hw) hm, hd.fderiv, ew_differential_cross]
  have hmetric : Surface.rho k w ^ 2 =
      ‖etaTarget k w‖ ^ 2 * (1 + ‖gauss k w‖ ^ 2) ^ 2 := by
    rw [← real_metric_eq_rho_sq hk w]
    exact Weierstrass.weierstrass_real_metric (gauss k w) (etaTarget k w)
  rw [hmetric, smul_smul]
  have hh : ‖etaTarget k w‖ ≠ 0 := norm_ne_zero_iff.mpr (etaTarget_ne_zero hk hw)
  have hg : 1 + ‖gauss k w‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  apply Prod.ext
  · simp only [stereoNormal, Prod.smul_fst, smul_eq_mul]
    field_simp
  · apply Prod.ext <;>
      simp only [stereoNormal, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
      field_simp

/-- Paper ewcover(v), in the finite coordinate, for the actual immersion normal. -/
theorem stereoCoord_ew_chartUnitNormal {k : ℕ} (hk : 2 ≤ k)
    {X : ℂ → AmbientTriple} {w : ℂ} (hw : w ∉ Surface.punctures k)
    (hd : HasFDerivAt X (ewRealDifferential k w) w) :
    Spherical.stereoCoord (tripleToEuclidean (chartUnitNormal X w)) = w ^ (k - 1) := by
  rw [ew_chartUnitNormal_eq_stereoNormal hk hw hd, stereoCoord_stereoNormal]
  rfl

/-- The proper half-turn acting on the infinity-coordinate differential. -/
def normalHalfTurn (p : AmbientTriple) : AmbientTriple := (p.1, -p.2.1, -p.2.2)

lemma normalHalfTurn_smul (c : ℝ) (p : AmbientTriple) :
    normalHalfTurn (c • p) = c • normalHalfTurn p := by
  simp [normalHalfTurn]

lemma normalHalfTurn_cross (a b : AmbientTriple) :
    euclideanCross (normalHalfTurn a) (normalHalfTurn b) = normalHalfTurn (euclideanCross a b) := by
  ext <;> simp [euclideanCross, normalHalfTurn] <;> ring

lemma infinityRealDifferential_halfTurn (k : ℕ) (v d : ℂ) :
    infinityRealDifferential k v d = normalHalfTurn (ewRealDifferential k v d) := by
  simp only [infinityRealDifferential, ewRealDifferential, ContinuousLinearMap.prod_apply,
    realCoeffLinear_apply, mul_neg, Complex.neg_re, normalHalfTurn]

lemma normalized_ew_cross {k : ℕ} (hk : 2 ≤ k) {w : ℂ} (hw : w ∉ Surface.punctures k) :
    (Surface.rho k w ^ 2)⁻¹ •
      euclideanCross (ewRealDifferential k w 1) (ewRealDifferential k w Complex.I) =
    stereoNormal (gauss k w) := by
  have hd := (ewRealDifferential k w).hasFDerivAt (x := w)
  have hm : ∀ d : ℂ, euclideanSq (fderiv ℝ (ewRealDifferential k w) w d) =
      Surface.rho k w ^ 2 * ‖d‖ ^ 2 := by
    intro d
    rw [hd.fderiv, ewRealDifferential_metric hk]
  have he := ew_chartUnitNormal_eq_stereoNormal hk hw hd
  rw [chartUnitNormal_eq_inv_conformal (rho_sq_pos hk hw) hm, hd.fderiv] at he
  exact he

/-- The actual infinity-chart normal, including its regular center. -/
theorem infinity_chartUnitNormal_eq {k : ℕ} (hk : 2 ≤ k)
    {X : ℂ → AmbientTriple} {v : ℂ} (hv : v ∉ Surface.punctures k)
    (hd : HasFDerivAt X (infinityRealDifferential k v) v) :
    chartUnitNormal X v = normalHalfTurn (stereoNormal (gauss k v)) := by
  have hm : ∀ d : ℂ, euclideanSq (fderiv ℝ X v d) = Surface.rho k v ^ 2 * ‖d‖ ^ 2 := by
    intro d
    rw [hd.fderiv, infinityRealDifferential_metric hk]
  rw [chartUnitNormal_eq_inv_conformal (rho_sq_pos hk hv) hm, hd.fderiv,
    infinityRealDifferential_halfTurn, infinityRealDifferential_halfTurn,
    normalHalfTurn_cross, ← normalHalfTurn_smul, normalized_ew_cross hk hv]

lemma stereoNormal_inv {g : ℂ} (hg : g ≠ 0) :
    stereoNormal g⁻¹ = normalHalfTurn (stereoNormal g) := by
  have hn : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
  have hd : 1 + ‖g‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  ext <;>
    simp only [stereoNormal, normalHalfTurn, Complex.inv_re, Complex.inv_im,
      Complex.normSq_eq_norm_sq, norm_inv, inv_pow] <;>
    field_simp <;> ring

/-- The finite and infinity expressions for the normal agree on their overlap. -/
theorem infinity_chartUnitNormal_overlap {k : ℕ} (hk : 2 ≤ k)
    {X : ℂ → AmbientTriple} {v : ℂ} (hv : v ∉ Surface.punctures k) (hv0 : v ≠ 0)
    (hd : HasFDerivAt X (infinityRealDifferential k v) v) :
    chartUnitNormal X v = stereoNormal (gauss k v⁻¹) := by
  have hg : gauss k v ≠ 0 := pow_ne_zero _ hv0
  rw [infinity_chartUnitNormal_eq hk hv hd, gauss_inv, stereoNormal_inv hg]

/-- Infinity is the north pole of the Gauss sphere; totalized finite
stereographic division must not be mistaken for its extended value. -/
theorem infinity_chartUnitNormal_zero {k : ℕ} (hk : 2 ≤ k)
    {X : ℂ → AmbientTriple} (hd : HasFDerivAt X (infinityRealDifferential k 0) 0) :
    chartUnitNormal X 0 = (0, 0, 1) := by
  have hp : (0 : ℂ) ∉ Surface.punctures k :=
    not_puncture_of_norm_lt_one hk (by simp)
  rw [infinity_chartUnitNormal_eq hk hp hd]
  simp [gauss, show k - 1 ≠ 0 by omega, stereoNormal, normalHalfTurn]

end KsIndex.KarcherData
